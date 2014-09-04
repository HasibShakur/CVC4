//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "util/QuantifierEliminate.h"
#include "expr/attribute.h"
#include "printer/smt2/smt2_printer.h"
#include "util/output.h"
#include "theory/rewriter.h"
#include "theory/arith/normal_form.h"
#include "util/rational.h"
#include "util/integer.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;
using namespace CVC4::theory::arith;

struct QENestedQuantAttributeId {
};
typedef expr::Attribute<QENestedQuantAttributeId, Node> QuantAttrib;

bool QuantifierEliminate::isLiteralQE(Node n) {
  switch(n.getKind()) {
  case kind::NOT:
    return isLiteralQE(n[0]);
    break;
  case kind::OR:
  case kind::AND:
  case kind::IMPLIES:
  case kind::XOR:
  case kind::ITE:
  case kind::IFF:
    return false;
    break;
  default:
    break;
  }
  return true;
}
bool QuantifierEliminate::isRelationalOperatorTypeQE(Kind k) {
  switch(k) {
  case kind::LT:
  case kind::GT:
  case kind::LEQ:
  case kind::GEQ:
  case kind::EQUAL:
    return true;
  default:
    return false;
  }
}

Node QuantifierEliminate::eliminateImpliesQE(Node body)
{
  if( isLiteralQE( body ) ){
      return body;
    }else{
      bool childrenChanged = false;
      std::vector< Node > children;
      for( unsigned i=0; i<body.getNumChildren(); i++ ){
        Node c = eliminateImpliesQE( body[i] );
        if( i==0 && ( body.getKind()== kind::IMPLIES ) ){
          c = c.negate();
        }
        children.push_back( c );
        childrenChanged = childrenChanged || c!=body[i];
      }
      if( body.getKind()== kind::IMPLIES ){
        return NodeManager::currentNM()->mkNode( OR, children );
      }else if( childrenChanged ){
        return NodeManager::currentNM()->mkNode( body.getKind(), children );
      }else{
        return body;
      }
    }
}

Node QuantifierEliminate::convertToPrenexQE(Node body, std::vector<Node>& args,
                                            bool pol) {
  if(body.getKind() == kind::FORALL) {
    if(pol) {
      std::vector<Node> terms;
      std::vector<Node> subs;
      for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
        //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
        terms.push_back(body[0][i]);
        subs.push_back(
            NodeManager::currentNM()->mkBoundVar(body[0][i].getType()));
      }
      args.insert(args.end(), subs.begin(), subs.end());
      Node newBody = body[1];
      newBody = newBody.substitute(terms.begin(), terms.end(), subs.begin(),
                                   subs.end());
      if(newBody.isNull()) {
        Debug("expr-qe") << "newBody is null in convertToPrenex" << "\n";
      }
      //  Debug("expr-qe") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << "\n";
      return newBody;
    } else {
      return body;
    }
  } else if(body.getKind() == kind::ITE || body.getKind() == kind::XOR
      || body.getKind() == kind::IFF) {
    return body;
  } else {
    Assert( body.getKind()!= kind::EXISTS );
    bool childrenChanged = false;
    std::vector<Node> newChildren;
    for(int i = 0; i < (int) body.getNumChildren(); i++) {
      bool newPol = body.getKind() == kind::NOT ? !pol : pol;
      Node n = convertToPrenexQE(body[i], args, newPol);
      newChildren.push_back(n);
      if(n != body[i]) {
        childrenChanged = true;
      }
    }
    if(childrenChanged) {
      if(body.getKind() == NOT && newChildren[0].getKind() == kind::NOT) {
        return newChildren[0][0];
      } else {
        return NodeManager::currentNM()->mkNode(body.getKind(), newChildren);
      }
    } else {
      return body;
    }
  }
}
/*Node QuantifierEliminate::convertToNNFQE(Node body)
 {
 if( body.getKind()== kind::NOT ){
 if( body[0].getKind()== kind::NOT ){
 Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][0].getKind() << "\n";
 return convertToNNFQE( body[0][0] );
 }else if( isLiteralQE( body[0] ) ){
 Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getKind() << "\n";
 return body;
 }else{
 std::vector< CVC4::Node > children;
 Kind k = body[0].getKind();
 Debug("expr-qetest") << "Inside NNF convertion of the formula kind (as per the given input it should be and) "<< k << "\n";
 if( body[0].getKind()== kind::OR || body[0].getKind()== kind::AND ){
 Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getNumChildren() << "\n";
 for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
 Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][i].getKind() << "\n";
 children.push_back( convertToNNFQE( body[0][i].notNode() ) );
 }
 Debug("expr-qetest") << "Size of children here "<< children.size() << "\n";
 k = body[0].getKind()== kind::AND ? kind::OR : kind::AND;
 }else if( body[0].getKind()== kind::IFF ){
 for( int i=0; i<2; i++ ){
 Node nn = i==0 ? body[0][i] : body[0][i].notNode();
 children.push_back( convertToNNFQE( nn ) );
 }
 }else if( body[0].getKind()== kind::ITE ){
 for( int i=0; i<3; i++ ){
 Node nn = i==0 ? body[0][i] : body[0][i].notNode();
 children.push_back( convertToNNFQE( nn ) );
 }
 }else{
 Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
 return body;
 }
 return NodeManager::currentNM()->mkNode( k, children );
 }
 }else if( isLiteralQE( body ) ){
 return body;
 }else{
 std::vector< CVC4::Node > children;
 bool childrenChanged = false;
 for( int i=0; i<(int)body.getNumChildren(); i++ ){
 Node nc = convertToNNFQE( body[i] );
 children.push_back( nc );
 childrenChanged = childrenChanged || nc!=body[i];
 }
 if( childrenChanged ){
 return NodeManager::currentNM()->mkNode( body.getKind(), children );
 }else{
 return body;
 }
 }
 }*/
Node QuantifierEliminate::convertToNNFQE(Node body, NodeManager* currNM) {

  if(body.getKind() == kind::NOT) {
    if(body[0].getKind() == kind::NOT) {
      //  Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][0].getKind() << "\n";
      return convertToNNFQE(body[0][0], currNM);
    } else if(isLiteralQE(body[0])) {
      //  Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getKind() << "\n";
      return body;
    } else {
      std::vector<CVC4::Node> children;
      Kind k = body[0].getKind();
      if(body[0].getKind() == kind::OR || body[0].getKind() == kind::AND) {
        for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
         /* if(isRelationalOperatorTypeQE(body[0][i].getKind())) {
            if(body[0][i].getKind() == kind::GEQ) {
              std::vector<CVC4::Node> children_relation;
              for(int j = 0; j < (int) body[0][i].getNumChildren(); j++) {
                children_relation.push_back(body[0][i][j]);
              }
              Node lt = currNM->mkNode(kind::LT, children_relation[0],
                                       children_relation[1]);
              children.push_back(convertToNNFQE(lt.notNode(),currNM));
            } else if(body[0][i].getKind() == kind::LEQ) {
              std::vector<CVC4::Node> children_relation;
              for(int j = 0; j < (int) body[0][i].getNumChildren(); j++) {
                children_relation.push_back(body[0][i][j]);
              }
              Node gt = currNM->mkNode(kind::GT, children_relation[0],
                                       children_relation[1]);
              children.push_back(convertToNNFQE(gt.notNode(),currNM));
            } else if(body[0][i].getKind() == kind::GT) {
              std::vector<CVC4::Node> children_relation;
              for(int j = 0; j < (int) body[0][i].getNumChildren(); j++) {
                children_relation.push_back(body[0][i][j]);
              }
              Node leq = currNM->mkNode(kind::LEQ, children_relation[0],
                                        children_relation[1]);
              children.push_back(convertToNNFQE(leq.notNode(),currNM));
            } else if(body[0][i].getKind() == kind::LT) {
              std::vector<CVC4::Node> children_relation;
              for(int j = 0; j < (int) body[0][i].getNumChildren(); j++) {
                children_relation.push_back(body[0][i][j]);
              }
              Node geq = currNM->mkNode(kind::GEQ, children_relation[0],
                                        children_relation[1]);
              children.push_back(convertToNNFQE(geq.notNode(),currNM));
            }
          }*/
          children.push_back( convertToNNFQE( body[0][i].notNode(),currNM ) );
        }
        k = body[0].getKind() == kind::AND ? kind::OR : kind::AND;
        Debug("expr-qetest")<<"New kind after negation "<<k<<"\n";
      }
      else {
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return currNM->mkNode(k, children);
    }
  } else if(isLiteralQE(body)) {
    return body;
  } else {
    std::vector<CVC4::Node> children;
    bool childrenChanged = false;
    for(int i = 0; i < (int) body.getNumChildren(); i++) {
      Node nc = convertToNNFQE(body[i], currNM);
      children.push_back(nc);
      childrenChanged = childrenChanged || nc != body[i];
    }
    if(childrenChanged) {
      return currNM->mkNode(body.getKind(), children);
    } else {
      return body;
    }
  }
}
Node QuantifierEliminate::internalProcessNodeQE(Node n)
{
  if(n.getKind()== kind::CONST_RATIONAL)
  {
   /* Constant c = Constant::mkConstant(n);
    Debug("expr-qetest")<<"Constant Node "<<c<<"\n";
    Constant one = Constant::mkOne();
    Debug("expr-qetest")<<"One Node "<<one<<"\n";
    Constant result = Constant::mkConstant(c.getValue()+one.getValue());
    return result.getNode();*/
    Debug("expr-qetest")<<"Constant "<<n.getType()<<"\n";
    Debug("expr-qetest")<<"Constant value "<<n.getType(true).getConst<Integer><<"\n";

   // Debug("expr-qetest")<<"Constant "<<n.getType(true).getConst()<<"\n";
    return n;
   }
  else
  {
    Debug("expr-qetest")<<"Print the kind "<<n.getKind()<<"\n";
    Debug("expr-qetest")<<"Print the kind "<<n.getType()<<"\n";
    Constant one = Constant::mkOne();
    NodeBuilder<> nb(kind::PLUS);
    nb << n << one.getNode();
    n = nb;
    Debug("expr-qetest")<<"Print the new node "<<n<<"\n";
    return n;
  }
}

Node QuantifierEliminate::replaceGEQQE(Node n,bool negationEnabled)
{
  Node leftChild;
  Node rightChild;
  Node replaceMent;
  if(negationEnabled)
  {
    leftChild = n[0];
    rightChild = n[1];
    replaceMent =  NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing GEQ with not "<<replaceMent<<"\n";
    return replaceMent;
  }
  else
  {
    leftChild = n[1];
    rightChild = QuantifierEliminate::internalProcessNodeQE(n[0]);
    Debug("expr-qetest")<<"After modification Right child "<<rightChild<<"\n";
    replaceMent = NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing GEQ without not "<<replaceMent<<"\n";
    return replaceMent;
  }
}

Node QuantifierEliminate::replaceGTQE(Node n,bool negationEnabled)
{
  Node leftChild;
  Node rightChild;
  Node replaceMent;
  if(negationEnabled)
  {
    leftChild = n[0];
    rightChild = QuantifierEliminate::internalProcessNodeQE(n[1]);
    Debug("expr-qetest")<<"After modification right child "<<rightChild<<"\n";
    replaceMent = NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing GT with not "<<replaceMent<<"\n";
    return replaceMent;
  }
  else
  {
    leftChild = n[1];
    rightChild = n[0];
    replaceMent = NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing GT without not "<<replaceMent<<"\n";
    return replaceMent;
  }
}

Node QuantifierEliminate::replaceLTQE(Node n,bool negationEnabled)
{
  Node leftChild;
  Node rightChild;
  Node replaceMent;
  if(negationEnabled)
  {
    leftChild = n[1];
    rightChild = QuantifierEliminate::internalProcessNodeQE(n[0]);
    Debug("expr-qetest")<<"After modification Right child "<<rightChild<<"\n";
    replaceMent = NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing LT with not "<<replaceMent<<"\n";
    return replaceMent;
  }
  else
  {
    replaceMent = n;
    Debug("expr-qetest")<<"After replacing LT without not "<<replaceMent<<"\n";
    return replaceMent;
  }
}

Node QuantifierEliminate::replaceLEQQE(Node n,bool negationEnabled)
{
  Node leftChild;
  Node rightChild;
  Node replaceMent;
  if(negationEnabled)
  {
    leftChild = n[1];
    rightChild = n[0];
    replaceMent = NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing LEQ with not "<<replaceMent<<"\n";
    return replaceMent;
  }
  else
  {
    leftChild = n[0];
    rightChild = QuantifierEliminate::internalProcessNodeQE(n[1]);
    Debug("expr-qetest")<<"After modification Right child "<<rightChild<<"\n";
    replaceMent = NodeManager::currentNM()->mkNode(kind::LT,leftChild,rightChild);
    Debug("expr-qetest")<<"After replacing LEQ without not "<<replaceMent<<"\n";
    return replaceMent;
  }
}

/*Node QuantifierEliminate::replaceEqualQE(Node n,bool negationEnabled)
{
  Debug("expr-qetest")<<n<<"\n";
  Node leftChild = n[0];
  Node rightChild = n[1];
  Node leftExp;
  Node rightExp;
  if(negationEnabled)
  {
    leftExp = NodeManager::currentNM()->mkNode(kind::LT, leftChild,rightChild);
    rightExp = NodeManager::currentNM()->mkNode(kind::LT, rightChild,leftChild);
    return NodeManager::currentNM()->mkNode(kind::OR, left,right);
  }
  else
  {
    Node modifiedLeftChild = QuantifierEliminate::internalProcessNodeQE(leftChild);
    Debug("expr-qetest")<<"After modification Left child "<<modifiedLeftChild<<"\n";
    Node modifiedRightChild = QuantifierEliminate::internalProcessNodeQE(rightChild);
    Debug("expr-qetest")<<"After modification Left child "<<modifiedRightChild<<"\n";
    leftExp = NodeManager::currentNM()->mkNode(kind::LT, leftChild, modifiedRightChild);
    Debug("expr-qetest")<<"Left Expression "<<leftExp<<"\n";
    rightExp = NodeManager::currentNM()->mkNode(kind::LT,rightChild,modifiedLeftChild);
    Debug("expr-qetest")<<"Right Expression "<<rightExp<<"\n";
    return NodeManager::currentNM()->mkNode(kind::AND, leftExp,rightExp);
  }
}*/

Node QuantifierEliminate::processRelationOperatorQE(Node n,bool negationEnabled)
{
  Node changedNode;
  if(negationEnabled)
  {
    if(n.getKind() == kind::GEQ)
    {
      changedNode = QuantifierEliminate::replaceGEQQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications of GEQ with not "<< changedNode<<"\n";
    }
    else if(n.getKind() == kind::GT)
    {
      changedNode = QuantifierEliminate::replaceGTQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications GT with not "<<changedNode<<"\n";
    }
    else if(n.getKind() == kind::LT)
    {
      changedNode = QuantifierEliminate::replaceLTQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications LT with not "<<changedNode<<"\n";
    }
    else if(n.getKind() == kind::LEQ)
    {
      changedNode = QuantifierEliminate::replaceLEQQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications LEQ with not "<<changedNode<<"\n";
    }
  /*  else if(n.getKind() == kind::EQUAL)
    {
      n = QuantifierEliminate::replaceEqualQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications "<<" "<<n<<"\n";
    }*/
  }
  else
  {
    if(n.getKind() == kind::GT)
    {
      changedNode = QuantifierEliminate::replaceGTQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications GT with not "<<changedNode<<"\n";
    }
    if(n.getKind() == kind::GEQ)
    {
      changedNode = QuantifierEliminate::replaceGEQQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications GEQ without not "<<changedNode<<"\n";
    }
    else if(n.getKind() == kind::LT)
    {
      changedNode = QuantifierEliminate::replaceLTQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications LT without not "<<changedNode<<"\n";
    }
    else if(n.getKind() == kind::LEQ)
    {
      changedNode = QuantifierEliminate::replaceLEQQE(n,negationEnabled);
      Debug("expr-qetest")<<"After modifications LEQ without not "<<changedNode<<"\n";
    }
//    else if(n.getKind() == kind::EQUAL)
//    {
//      n = QuantifierEliminate::replaceEqualQE(n,negationEnabled);
//      Debug("expr-qetest")<<"After modifications "<<" "<<n<<"\n";
//    }
  }
  return changedNode;
}

Node QuantifierEliminate::doRewriting(Node n,NodeManager* currNM)
{
  Node processedFirstChild;
  Node processedSecondChild;
  Node finalNode;
  if(n.getKind() == kind::OR || n.getKind() == kind::AND)
  {
    if(n[0].getKind() == kind::NOT)
    {
      Debug("expr-qetest") << "Before processing first child "<< n[0]<<"\n";
      processedFirstChild = QuantifierEliminate::processRelationOperatorQE(n[0][0], true);
      Debug("expr-qetest") << "After processing first child "<< processedFirstChild<<"\n";
    }
    else
    {
      Debug("expr-qetest") << "Before processing first child "<< n[0]<<"\n";
      processedFirstChild = QuantifierEliminate::processRelationOperatorQE(n[0],false);
      Debug("expr-qetest") << "After processing first child "<< processedFirstChild<<"\n";
    }
    if(n[1].getKind() == kind::NOT)
    {
      Debug("expr-qetest") << "Before processing second child "<< n[1]<<"\n";
      processedSecondChild = QuantifierEliminate::processRelationOperatorQE(n[1][0],true);
      Debug("expr-qetest") << "After processing second child "<< processedSecondChild<<"\n";
    }
    else
    {
      Debug("expr-qetest") << "Before processing second child "<< n[1]<<"\n";
      processedSecondChild = QuantifierEliminate::processRelationOperatorQE(n[1],false);
      Debug("expr-qetest") << "After processing second child "<< processedSecondChild<<"\n";
    }
    NodeBuilder<> nb(n.getKind());
    nb<<processedFirstChild<<processedSecondChild;
    finalNode = nb;
    Debug("expr-qetest") << "After processing final node "<< finalNode<<"\n";
    return finalNode;
  }
  else
  {
    Debug("expr-qetest") << "Process Relational Operator Directly "<< "\n";
    Node finalNode;
    if(n.getKind() == kind::NOT)
    {
      Debug("expr-qetest") << "Node to process "<< n<<"\n";
      finalNode = QuantifierEliminate::processRelationOperatorQE(n[0],true);
      Debug("expr-qetest") << "After processing final node "<< finalNode<<"\n";
    }
    else
    {
      Debug("expr-qetest") << "Node to process "<< n<<"\n";
      finalNode = QuantifierEliminate::processRelationOperatorQE(n,false);
      Debug("expr-qetest") << "After processing final node "<< finalNode<<"\n";
    }
    return finalNode;
  }
}

Node QuantifierEliminate::doPreprocessing(Expr ex) {
  Node temp_in = NodeTemplate<true>(ex);
  Debug("expr-qetest") << "------- Inside doProcessing Method ------" << "\n";
  Node in;
  if(temp_in.getKind() == kind::NOT) {
    in = temp_in[0];
  } else {
    in = temp_in;
  }
  if(in.getKind() == kind::FORALL) {
    std::vector<Node> args;
    for(int i = 0; i < (int) in[0].getNumChildren(); i++) {
      args.push_back(in[0][i]);
    }
    NodeBuilder<> defs(kind::AND);
    Node n = in[1];
    Node ipl;
    if(in.getNumChildren() == 3) {
      ipl = in[2];
    }
    if(n.isNull()) {
      Debug("expr-qetest") << "Node n is null in doPreprocessing after Node n = in[1]" << "\n";
    }
    n = eliminateImpliesQE(n);
    Debug("expr-qetest") << "After After Eliminating Implies "<< n << "\n";
    n = convertToPrenexQE(n, args, true);
    Debug("expr-qetest") << "After Prenexing "<< n << "\n";
    if(n.isNull()) {
      Debug("expr-qetest") << "Node n is null in doPreprocessing after Node n = convertToPrenexQE(n,args, true)" << "\n";
    }
    NodeManager* currNM = NodeManager::currentNM();
    Node nnfNode = convertToNNFQE(n, currNM);
    Debug("expr-qetest") << "After nnf "<< nnfNode << "\n";
    if(nnfNode.isNull()) {
      Debug("expr-qetest") << "Node rewrittenNode is null in doPreprocessing after rewriting " << "\n";
    }
    Node rewrittenNode = doRewriting(nnfNode,currNM);
    Debug("expr-qetest") << "After rewriting "<< rewrittenNode << "\n";
    if(rewrittenNode.isNull()) {
       Debug("expr-qetest") << "Node rewrittenNode is null in doPreprocessing after rewriting " << "\n";
    }
    if(in[1] == rewrittenNode && args.size() == in[0].getNumChildren()) {
      return in;
    } else {
      if(args.empty()) {
        defs << rewrittenNode;
      } else {
        std::vector<Node> children;
        children.push_back(
            NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args));
        children.push_back(rewrittenNode);
        if(!ipl.isNull()) {
          children.push_back(ipl);
        }
        defs << NodeManager::currentNM()->mkNode(kind::FORALL, children);
      }
      Node returnNode =
          defs.getNumChildren() == 1 ? defs.getChild(0) : defs.constructNode();
      if(temp_in.getKind() == kind::NOT) {
        std::vector<Node> children;
        children.push_back(returnNode);
        return NodeManager::currentNM()->mkNode(kind::NOT, children);
      } else {
        return returnNode;
      }
    }
  } else {
    return in;
  }
}


/*CVC4::Node QuantifierEliminate::normalizeBody(CVC4::Node body)
 {
 bool rewritten = false;
 Node normalized;
 for(int i=0;i<(int)body.getNumChildren();i++)
 {
 if(body[i].getKind() == NOT)
 {
 //If it is not then do the normalization of the expression whose kind is not
 //Just call the negateNode on the simplification done on the else part
 }
 else
 {
 // If it is not of the kind not then directly normalize this
 if(this->isLiteral(body[i]))
 {
 // If it is a literal then we need to do nothing
 rewritten = false;
 }
 else if(body[i].getKind()==EQUAL)
 {
 //  body[i].kinded_iterator::begin(body[i],EQUAL);
 }
 // If the operator is > then convert it to < by just exchanging the operators then making a node using mkNode
 // If the operator is = then use the following conversion s=t <==> s>t+1 and t>s+1
 }
 }
 if(!rewritten)
 {
 return body;
 }
 else
 {
 return normalized;
 }
 }*/
/*Node QuantifierEliminate::simplifyExpression(Node n)
 {
 // 1st phase of simplification is converting the expression to NNF
 Node nnfNode = convertToNNF(n);
 // 3rd phase of simplification is applying the replace rules
 //Node normalizedBody = normalizeBody(nnfNode);
 // 4th phase of simplification is
 return nnfNode;
 }*/
/*bool QuantifierEliminate::isClauseQE( Node n ){
 if( isLiteralQE( n ) ){
 return true;
 }else if( n.getKind()==kind::NOT ){
 return isCubeQE( n[0] );
 }else if( n.getKind()==kind::OR ){
 for( int i=0; i<(int)n.getNumChildren(); i++ ){
 if( !isClauseQE( n[i] ) ){
 return false;
 }
 }
 return true;
 }else if( n.getKind()==kind::IMPLIES ){
 return isCubeQE( n[0] ) && isClauseQE( n[1] );
 }else{
 return false;
 }
 }*/
