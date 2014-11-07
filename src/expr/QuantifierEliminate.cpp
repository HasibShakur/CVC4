//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "expr/QuantifierEliminate.h"
#include "expr/attribute.h"
#include "printer/smt2/smt2_printer.h"
#include "util/output.h"
#include "theory/rewriter.h"
#include "theory/arith/normal_form.h"
#include "util/rational.h"
#include "util/integer.h"
#include "theory/arith/arith_utilities.h"
//#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
//using namespace CVC4::theory::quantifiers;

//struct QENestedQuantAttributeId {
//};
//typedef expr::Attribute<QENestedQuantAttributeId, Node> QuantAttrib;

std::vector<std::vector<Node> > QuantifierEliminate::boundVar;
std::vector<Node> QuantifierEliminate::args;

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
bool QuantifierEliminate::isConstQE(Node n)
{
  if(n.isConst())
    return true;
  else
    return false;
}
bool QuantifierEliminate::isVarQE(Node n)
{
  if(n.isVar() && n.getType().isInteger() )
    return true;
  else
    return false;
}
bool QuantifierEliminate::isVarWithCoefficientsQE(Node n)
{
  if(n.getKind()==kind::MULT && (isVarQE(n[0]) || isConstQE(n[0])) && (isVarQE(n[1])||isConstQE(n[1])))
  {
    return true;
  }
  else
  {
    return false;
  }
}
bool QuantifierEliminate::isEquationQE(Node n)
{
  if(isRelationalOperatorTypeQE(n.getKind()))
    return true;
  else
    return false;
}

Node QuantifierEliminate::returnCoefficientQE(Node n)
{
  if(isVarWithCoefficientsQE(n))
  {
    return n[0];
  }
  else
  {
    return n;
  }
}

//void QuantifierEliminate::setQENestedQuantifiers(Node n, Node q) {
//  std::vector<Node> processed;
//  setQENestedQuantifiers2(n, q, processed);
//}
//
//void QuantifierEliminate::setQENestedQuantifiers2(Node n, Node q, std::vector<Node>& processed) {
//  if(std::find(processed.begin(), processed.end(), n) == processed.end()) {
//    processed.push_back(n);
//    if(n.getKind() == kind::FORALL || n.getKind() == kind::EXISTS) {
//      Debug("expr-qetest") << "Set nested quant attribute " << n << std::endl;
//      QuantAttrib qenq;
//     // n[0].setAttribute(qenq,q);
//      n[0].setAttribute(qenq,q);
//    }
//    for(int i = 0; i < (int) n.getNumChildren(); i++) {
//      setQENestedQuantifiers2(n[i], q, processed);
//    }
//  }
//}

//void QuantifierEliminate::setAttributesQE(Node in, Node n) {
//  if((n.getKind() == kind::FORALL || n.getKind() == kind::EXISTS)
//      && (in.getKind() == kind::FORALL || in.getKind() == kind::EXISTS)) {
//    if(in[0].hasAttribute(QuantAttrib())) {
//      setQENestedQuantifiers(n[0], in[0].getAttribute(QuantAttrib()));
//    }
//  }
//}

//Node QuantifierEliminate::preRewriteForPrenex(Node in) {
//  Node temp;
//  if(in.getKind() == kind::NOT) {
//    temp = in[0];
//  } else {
//    temp = in;
//  }
//  if(temp.getKind() == kind::EXISTS || temp.getKind() == kind::FORALL) {
//    Debug("expr-qetest") << "pre-rewriting for prenexing" << temp << " " << temp[0].hasAttribute(QuantAttrib()) << std::endl;
//    if( !temp.hasAttribute(QuantAttrib()) ) {
//      setQENestedQuantifiers( temp[ 1 ], temp );
//    }
//    std::vector< Node > args;
//    for( int i=0; i<(int)temp[0].getNumChildren(); i++ ) {
//      args.push_back( temp[0][i] );
//      Debug("expr-qetest") << "Element" <<i<<" "<< args.back() <<std::endl;
//    }
//    Node body = temp[1];
//    Debug("expr-qetest") << "Initial body "<<body<<std::endl;
//    bool doRewrite = false;
//    while( body.getNumChildren()>=2 && body.getKind()==temp.getKind() ) {
//      for( int i=0; i<(int)body[0].getNumChildren(); i++ ) {
//        args.push_back( body[0][i] );
//        Debug("expr-qetest") << "Element" <<i<<" "<< args.back() <<std::endl;
//      }
//      body = body[1];
//      Debug("expr-qetest") << "new body "<<body<<std::endl;
//      doRewrite = true;
//    }
//    if( doRewrite ) {
//      std::vector< Node > children;
//      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,args) );
//      children.push_back( body );
//      if( temp.getNumChildren()==3 ) {
//        children.push_back( temp[2] );
//      }
//      Node n = NodeManager::currentNM()->mkNode( temp.getKind(), children );
//      if( temp!=n ) {
//        setAttributesQE( temp, n );
//        Debug("expr-qetest") << "*** pre-rewrite for prenexing " << temp << std::endl;
//        Debug("expr-qetest") << " to " << std::endl;
//        Debug("expr-qetest") << n << std::endl;
//      }
//      if(in.getKind() == kind::NOT)
//      {
//        return n.notNode();
//      }
//      else
//      {
//        return n;
//      }
//    }
//    return in;
//  }
//  return in;
//}
//Node QuantifierEliminate::computeOperationQE(Node f, bool isNested)
//{
//  if( (f.getKind()==kind::EXISTS) || (f.getKind() == kind::FORALL) ){
//      Debug("expr-qetest") << "Compute operation on " << f << ", nested = " << isNested << std::endl;
//      std::vector< Node > args;
//      for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
//        args.push_back( f[0][i] );
//      }
//      NodeBuilder<> defs(kind::AND);
//      Node n = f[1];
//      Node ipl;
//      if( f.getNumChildren()==3 ){
//        ipl = f[2];
//      }
//      Debug("expr-qetest")<<"Body "<<n<<std::endl;
//      n = eliminateImpliesQE(n);
//      Debug("expr-qetest")<<"After eliminate Implies call "<<n<<std::endl;
//      n = convertToNNFQE(n);
//      n = convertToPrenexQE(n,args,true);
//      Debug("expr-qetest")<<"Prenex Body "<<n<<std::endl;
//     Debug("expr-qetest") << "Compute Operation: return " << n << ", " << args.size() << std::endl;
//      if( f[1]==n && args.size()==f[0].getNumChildren() ){
//        return f;
//      }else{
//        if( args.empty() ){
//          defs << n;
//        }else{
//          std::vector< Node > children;
//          children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
//          children.push_back( n );
//          if( !ipl.isNull() ){
//            children.push_back( ipl );
//          }
//          defs << NodeManager::currentNM()->mkNode(f.getKind(), children );
//        }
//        return defs.getNumChildren()==1 ? defs.getChild( 0 ) : defs.constructNode();
//      }
//    }else{
//      return f;
//    }
//}

//Node QuantifierEliminate::postRewriteForPrenex(Node in) {
//  /*Debug("expr-qetest") << "post-rewriting for prenex " << in << std::endl;
//  Debug("expr-qetest") << "Attributes : " << in[0].hasAttribute(QuantAttrib()) << std::endl;
//  //  if( !options::quantRewriteRules() || !TermDb::isRewriteRule( in ) ){
//  bool rewriteStat = true;
//  while(rewriteStat)
//  {
//    Node ret = in;
//    //get the arguments
//    std::vector< Node > args;
//    for( int i=0; i<(int)in[0].getNumChildren(); i++ ) {
//      args.push_back( in[0][i] );
//    }
//    for( int i=0; i<args.size(); i++ ) {
//      Debug("expr-qetest") << "element at "<<i<<" " << args.back() << std::endl;
//    }
//    //get the instantiation pattern list
//    Node ipl;
//    if( in.getNumChildren()==3 ) {
//      ipl = in[2];
//    }
//    //get the body
//    if( in.getKind()==kind::FORALL ) {
//      std::vector< Node > children;
//      children.push_back( in[0] );
//      children.push_back( in[1].negate() );
//      if( in.getNumChildren()==3 ) {
//        children.push_back( in[2] );
//      }
//      ret = NodeManager::currentNM()->mkNode( kind::EXISTS, children );
//      ret = ret.negate();
//      rewriteStat = true;
//    }
//      bool isNested = in[0].hasAttribute(QuantAttrib());
//      ret = computeOperationQE( in, isNested);
//      if( ret!=in ) {
//        rewriteStat = false;
//        break;
//      }
//    if(in != ret)
//    {
//      setAttributesQE(in,ret);
//      Debug("expr-qetest") << "*** rewrite " << in << std::endl;
//      Debug("expr-qetest") << " to " << std::endl;
//      Debug("expr-qetest") << ret << std::endl;
//    }
//    return ret;
//  }
//  return in;*/
//  Node ret = in;
//  //ret = replaceForall(ret);
//  //Debug("expr-qetest") << "After converting all the forall to exists " << ret << std::endl;
//  bool isNested = in[0].hasAttribute(QuantAttrib());
//  ret = computeOperationQE( ret, true);
//  Debug("expr-qetest") << "After computeOperation " << ret << std::endl;
//  return ret;
//}

//Node QuantifierEliminate::replaceForall(Node body)
//{
//  if(isLiteralQE(body))
//  {
//    return body;
//  }
//  else
//  {
//    bool childrenChanged = false;
//        std::vector<Node> children;
//    for(unsigned i = 0; i < body.getNumChildren(); i++) {
//      Node c = replaceForall(body[i]);
//      if(i == 0 && (body.getKind() == kind::FORALL)) {
//        c = c.negate();
//      }
//      children.push_back(c);
//      childrenChanged = childrenChanged || c != body[i];
//    }
//    if(body.getKind() == kind::FORALL) {
//          Node temp = NodeManager::currentNM()->mkNode(kind::NOT,children);
//          Debug("expr-qetest") << "After not " << temp << std::endl;
//          return NodeManager::currentNM()->mkNode(kind::EXISTS, temp);
//        } else if(childrenChanged) {
//          return NodeManager::currentNM()->mkNode(body.getKind(), children);
//        } else {
//          return body;
//        }
//  }
//}

//Node QuantifierEliminate::eliminateImpliesQE(Node body) {
//  if(isLiteralQE(body)) {
//    return body;
//  } else {
//    bool childrenChanged = false;
//    std::vector<Node> children;
//    for(unsigned i = 0; i < body.getNumChildren(); i++) {
//      Node c = eliminateImpliesQE(body[i]);
//      if(i == 0 && (body.getKind() == kind::IMPLIES)) {
//        c = c.negate();
//      }
//      children.push_back(c);
//      childrenChanged = childrenChanged || c != body[i];
//    }
//    if(body.getKind() == kind::IMPLIES) {
//      return NodeManager::currentNM()->mkNode(OR, children);
//    } else if(childrenChanged) {
//      return NodeManager::currentNM()->mkNode(body.getKind(), children);
//    } else {
//      return body;
//    }
//  }
//}

//Node QuantifierEliminate::convertToPrenexQE(Node body, std::vector<Node>& args,
//                                            bool pol) {
//  if((body.getKind() == kind::EXISTS) || (body.getKind() == kind::FORALL)) {
//    if(pol) {
//      std::vector<Node> terms;
//      std::vector<Node> subs;
//      for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
//        //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
//        terms.push_back(body[0][i]);
//        subs.push_back(
//            NodeManager::currentNM()->mkBoundVar(body[0][i].getType()));
//      }
//      args.insert(args.end(), subs.begin(), subs.end());
//      Node newBody = body[1];
//      newBody = newBody.substitute(terms.begin(), terms.end(), subs.begin(),
//                                   subs.end());
//      if(newBody.isNull()) {
//        Debug("expr-qe") << "newBody is null in convertToPrenex" << "\n";
//      }
//      //  Debug("expr-qe") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << "\n";
//      return newBody;
//    } else {
//      return body;
//    }
//  } else if(body.getKind() == kind::ITE || body.getKind() == kind::XOR
//      || body.getKind() == kind::IFF) {
//    return body;
//  } else {
//   // Assert( body.getKind()!= kind::FORALL );
//    bool childrenChanged = false;
//    std::vector<Node> newChildren;
//    for(int i = 0; i < (int) body.getNumChildren(); i++) {
//      bool newPol = body.getKind() == kind::NOT ? !pol : pol;
//      Node n = convertToPrenexQE(body[i], args, newPol);
//      newChildren.push_back(n);
//      if(n != body[i]) {
//        childrenChanged = true;
//      }
//    }
//    if(childrenChanged) {
//      if(body.getKind() == NOT && newChildren[0].getKind() == kind::NOT) {
//        return newChildren[0][0];
//      } else {
//        return NodeManager::currentNM()->mkNode(body.getKind(), newChildren);
//      }
//    } else {
//      return body;
//    }
//  }
//}

//Node QuantifierEliminate::convertToNNFQE(Node body) {
//
//  if(body.getKind() == kind::NOT) {
//    if(body[0].getKind() == kind::NOT) {
//      //  Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][0].getKind() << "\n";
//      return convertToNNFQE(body[0][0]);
//    } else if(isLiteralQE(body[0])) {
//      //  Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getKind() << "\n";
//      return body;
//    } else {
//      std::vector<CVC4::Node> children;
//      Kind k = body[0].getKind();
//      if(body[0].getKind() == kind::OR || body[0].getKind() == kind::AND) {
//        for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
//          children.push_back(convertToNNFQE(body[0][i].notNode()));
//        }
//        k = body[0].getKind() == kind::AND ? kind::OR : kind::AND;
//        Debug("expr-qetest")<<"New kind after negation "<<k<<"\n";
//      }
//      else {
//        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
//        return body;
//      }
//      return NodeManager::currentNM()->mkNode(k, children);
//    }
//  } else if(isLiteralQE(body)) {
//    return body;
//  } else {
//    std::vector<CVC4::Node> children;
//    bool childrenChanged = false;
//    for(int i = 0; i < (int) body.getNumChildren(); i++) {
//      Node nc = convertToNNFQE(body[i]);
//      children.push_back(nc);
//      childrenChanged = childrenChanged || nc != body[i];
//    }
//    if(childrenChanged) {
//      return NodeManager::currentNM()->mkNode(body.getKind(), children);
//    } else {
//      return body;
//    }
//  }
//}

/*Node QuantifierEliminate::internalProcessNodeQE(Node n) {
 if(n.getKind() == kind::CONST_RATIONAL) {
 Debug("expr-qetest")<<"Constant "<<n.getType()<<"\n";
 Constant c = Constant::mkConstant(n);
 Constant one = Constant::mkOne();
 Debug("expr-qetest")<<"Constant value "<<(c+one).getValue()<<"\n";
 Node temp = (c+one).getNode();
 return temp;
 }
 else
 {
 Debug("expr-qetest")<<"Print the kind "<<n.getKind()<<"\n";
 Debug("expr-qetest")<<"Print the kind "<<n.getType()<<"\n";
 Debug("expr-qetest")<<"Print the Node "<<n<<"\n";
 Constant one = Constant::mkOne();
 NodeBuilder<> nb(kind::PLUS);
 nb << n << one.getNode();
 n = nb;
 Debug("expr-qetest")<<"Print the new node "<<n<<"\n";
 return n;
 }
 }

 Node QuantifierEliminate::normalizeAtom(Node n) {
 Node leftNode = n[0];
 Node rightNode = n[1];
 Node temp;
 if(leftNode.hasBoundVar()) {
 if(leftNode.getKind() == kind::PLUS) {
 //      for(Node::kinded_iterator i=leftNode.begin(leftNode.getKind()),
 //          i_end = leftNode.end(kind::MULT);
 //          i!=i_end;
 //          ++i)
 //      {
 //        temp =
 //      }
 if(leftNode[0].hasBoundVar()) {
 Rational negOne(-1);
 temp = NodeManager::currentNM()->mkNode(kind::MULT,
 mkRationalNode(negOne),
 leftNode[1]);
 leftNode = leftNode[0];
 NodeBuilder<> nb(kind::PLUS);
 nb << rightNode << temp;
 rightNode = nb;
 } else {
 Rational negOne(-1);
 temp = NodeManager::currentNM()->mkNode(kind::MULT,
 mkRationalNode(negOne),
 leftNode[0]);
 leftNode = leftNode[1];
 NodeBuilder<> nb(kind::PLUS);
 nb << rightNode << temp;
 rightNode = nb;
 }
 }
 } else if(rightNode.hasBoundVar()) {
 if(rightNode.getKind() == kind::PLUS) {
 if(rightNode[0].hasBoundVar()) {
 Rational negOne(-1);
 temp = NodeManager::currentNM()->mkNode(kind::MULT,
 mkRationalNode(negOne),
 rightNode[1]);
 rightNode = rightNode[0];
 NodeBuilder<> nb(kind::PLUS);
 nb << leftNode << temp;
 leftNode = nb;
 } else {
 Rational negOne(-1);
 temp = NodeManager::currentNM()->mkNode(kind::MULT,
 mkRationalNode(negOne),
 rightNode[0]);
 rightNode = rightNode[1];
 NodeBuilder<> nb(kind::PLUS);
 nb << leftNode << temp;
 leftNode = nb;
 }
 }
 }
 NodeBuilder<> returnNode(n.getKind());
 returnNode << leftNode << rightNode;
 return returnNode;
 }
 Node QuantifierEliminate::replaceGEQQE(Node n, bool negationEnabled) {
 Node leftChild;
 Node rightChild;
 Node replaceMent;
 if(negationEnabled) {
 leftChild = n[0];
 Debug("expr-qetest")<<"GEQ with not Left child "<<leftChild<<"\n";
 rightChild = n[1];
 Debug("expr-qetest")<<"GEQ with not Right child "<<rightChild<<"\n";
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing GEQ with not "<<replaceMent<<"\n";
 return replaceMent;
 } else {
 leftChild = n[1];
 Debug("expr-qetest")<<"GEQ without not Left child "<<leftChild<<"\n";
 rightChild = QuantifierEliminate::internalProcessNodeQE(n[0]);
 Debug("expr-qetest")<<"After modification Right child "<<rightChild<<"\n";
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing GEQ without not "<<replaceMent<<"\n";
 return replaceMent;
 }
 }

 Node QuantifierEliminate::replaceGTQE(Node n, bool negationEnabled) {
 Node leftChild;
 Node rightChild;
 Node replaceMent;
 if(negationEnabled) {
 leftChild = n[0];
 rightChild = QuantifierEliminate::internalProcessNodeQE(n[1]);
 Debug("expr-qetest")<<"After modification right child "<<rightChild<<"\n";
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing GT with not "<<replaceMent<<"\n";
 return replaceMent;
 } else {
 leftChild = n[1];
 rightChild = n[0];
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing GT without not "<<replaceMent<<"\n";
 return replaceMent;
 }
 }

 Node QuantifierEliminate::replaceLTQE(Node n, bool negationEnabled) {
 Node leftChild;
 Node rightChild;
 Node replaceMent;
 if(negationEnabled) {
 leftChild = n[1];
 rightChild = QuantifierEliminate::internalProcessNodeQE(n[0]);
 Debug("expr-qetest")<<"After modification Right child "<<rightChild<<"\n";
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing LT with not "<<replaceMent<<"\n";
 return replaceMent;
 } else {
 replaceMent = n;
 Debug("expr-qetest")<<"After replacing LT without not "<<replaceMent<<"\n";
 return replaceMent;
 }
 }

 Node QuantifierEliminate::replaceLEQQE(Node n, bool negationEnabled) {
 Node leftChild;
 Node rightChild;
 Node replaceMent;
 if(negationEnabled) {
 leftChild = n[1];
 rightChild = n[0];
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing LEQ with not "<<replaceMent<<"\n";
 return replaceMent;
 } else {
 leftChild = n[0];
 rightChild = QuantifierEliminate::internalProcessNodeQE(n[1]);
 Debug("expr-qetest")<<"After modification Right child "<<rightChild<<"\n";
 replaceMent = NodeManager::currentNM()->mkNode(kind::LT, leftChild,
 rightChild);
 Debug("expr-qetest")<<"After replacing LEQ without not "<<replaceMent<<"\n";
 return replaceMent;
 }
 }

 Node QuantifierEliminate::replaceEqualQE(Node n, bool negationEnabled) {
 Node leftNode = n[0];
 Node rightNode = n[1];
 if(negationEnabled) {
 NodeBuilder<> leftSide(kind::LT);
 leftSide << leftNode << rightNode;
 Debug("expr-qetest")<<"Left side of equality with not "<<leftSide<<"\n";
 NodeBuilder<> rightSide(kind::LT);
 rightSide << rightNode << leftNode;
 Debug("expr-qetest")<<"Right side of equality with not "<<rightSide<<"\n";
 Node tempLeft = QuantifierEliminate::normalizeAtom(leftSide);
 Debug("expr-qetest")<<"After Normalization(left side) "<< tempLeft<<"\n";
 Node tempRight = QuantifierEliminate::normalizeAtom(rightSide);
 Debug("expr-qetest")<<"After Normalization(right side) "<< tempRight<<"\n";
 NodeBuilder<> returnNode(kind::OR);
 returnNode << tempLeft << tempRight;
 Debug("expr-qetest")<<"Replacing equality with not "<<returnNode<<"\n";
 return returnNode;
 } else {
 Rational positiveOne(1);
 Node temp1 = NodeManager::currentNM()->mkNode(kind::PLUS, rightNode,
 mkRationalNode(positiveOne));
 NodeBuilder<> leftSide(kind::LT);
 leftSide << leftNode << temp1;
 Debug("expr-qetest")<<"Left side of equality "<<leftSide<<"\n";
 Node temp2 = NodeManager::currentNM()->mkNode(kind::PLUS, leftNode,
 mkRationalNode(positiveOne));
 NodeBuilder<> rightSide(kind::LT);
 rightSide << rightNode << temp2;
 Debug("expr-qetest")<<"Right side of equality "<<rightSide<<"\n";
 Node tempLeft = QuantifierEliminate::normalizeAtom(leftSide);
 Debug("expr-qetest")<<"After Normalization(left side) "<< tempLeft<<"\n";
 Node tempRight = QuantifierEliminate::normalizeAtom(rightSide);
 Debug("expr-qetest")<<"After Normalization(right side) "<< tempRight<<"\n";
 NodeBuilder<> returnNode(kind::AND);
 returnNode << tempLeft << tempRight;
 Debug("expr-qetest")<<"Replacing equality "<<returnNode<<"\n";
 return returnNode;
 }
 }*/

/*Node QuantifierEliminate::processRelationOperatorQE(Node n,
 bool negationEnabled) {
 Node changedNode;
 if(negationEnabled) {
 if(n.getKind() == kind::GEQ) {
 changedNode = QuantifierEliminate::replaceGEQQE(n, negationEnabled);
 Debug("expr-qetest")<<"After modifications of GEQ with not(Before Normalization) "<< changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications of GEQ with not(After Normalization) "<< changedNode<<"\n";
 }
 else if(n.getKind() == kind::GT)
 {
 changedNode = QuantifierEliminate::replaceGTQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications GT with not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications GT with not(After Normalization) "<< changedNode<<"\n";
 }
 else if(n.getKind() == kind::LT)
 {
 changedNode = QuantifierEliminate::replaceLTQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications LT with not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications LT with not(After Normalization) "<< changedNode<<"\n";
 }
 else if(n.getKind() == kind::LEQ)
 {
 changedNode = QuantifierEliminate::replaceLEQQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications LEQ with not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications LEQ with not(After Normalization) "<< changedNode<<"\n";
 }
 else if(n.getKind() == kind::EQUAL)
 {
 changedNode = QuantifierEliminate::replaceEqualQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications EQUAL with not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications EQUAL with not(After Normalization) "<< changedNode<<"\n";
 }
 }
 else
 {
 if(n.getKind() == kind::GT)
 {
 changedNode = QuantifierEliminate::replaceGTQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications GT without not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications GT without not(After Normalization) "<< changedNode<<"\n";
 }
 if(n.getKind() == kind::GEQ)
 {
 changedNode = QuantifierEliminate::replaceGEQQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications GEQ without not(Before Normalization)  "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications GEQ without not(After Normalization) "<< changedNode<<"\n";
 }
 else if(n.getKind() == kind::LT)
 {
 changedNode = QuantifierEliminate::replaceLTQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications LT without not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications LT without not(After Normalization) "<< changedNode<<"\n";

 }
 else if(n.getKind() == kind::LEQ)
 {
 changedNode = QuantifierEliminate::replaceLEQQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications LEQ without not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications LEQ without not(After Normalization) "<< changedNode<<"\n";
 }
 else if(n.getKind() == kind::EQUAL)
 {
 changedNode = QuantifierEliminate::replaceEqualQE(n,negationEnabled);
 Debug("expr-qetest")<<"After modifications EQUAL without not(Before Normalization) "<<changedNode<<"\n";
 changedNode = QuantifierEliminate::normalizeAtom(changedNode);
 Debug("expr-qetest")<<"After modifications EQUAL without not(After Normalization) "<< changedNode<<"\n";
 }
 }
 return changedNode;
 }*/
/*bool QuantifierEliminate::evaluateBoolean(Node n) {
 bool result = false;
 if(n[0].hasBoundVar()) {
 if(n[0].getKind() == kind::MULT) {
 result = false;
 Debug("expr-qetest") << "Result of evaluating "<< n<<" "<<result<<"\n";
 }
 else
 {
 result = true;
 Debug("expr-qetest") << "Result of evaluating "<< n<<" "<<result<<"\n";
 }
 }
 else
 {
 if(n[1].getKind() == kind::MULT)
 {
 result = true;
 Debug("expr-qetest") << "Result of evaluating "<< n<<" "<<result<<"\n";
 }
 else
 {
 result = false;
 Debug("expr-qetest") << "Result of evaluating "<< n<<" "<<result<<"\n";
 }
 }
 return result;
 }*/

/*Node QuantifierEliminate::doRewriting(Node n) {
 Node processedFirstChild;
 Node processedSecondChild;
 Node finalNode;
 // n = Rewriter::rewrite(n);
 if(n.getKind() == kind::OR || n.getKind() == kind::AND) {
 if(n[0].getKind() == kind::NOT) {
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
 bool QuantifierEliminate::computeLeftProjection(Node n) {
 Debug("expr-qetest")<<"Node before computing projection "<<n<<"\n";
 Debug("expr-qetest")<<"Number of Children "<<n.getNumChildren()<<"\n";
 bool result = true;
 for(int i=0;i<(int)n.getNumChildren();i++)
 {
 Debug("expr-qetest")<<"Child "<<i<<" "<<n[i]<<"\n";
 if((n[i].getKind()== kind::AND) || (n[i].getKind()== kind::OR))
 {
 bool temp1 = evaluateBoolean(n[i][0]);
 Debug("expr-qetest")<<"Left Projection for "<<n[i][0]<<" is "<<temp1<<"\n";
 bool temp2 = evaluateBoolean(n[i][1]);
 Debug("expr-qetest")<<"Left Projection for "<<n[i][1]<<" is "<<temp2<<"\n";
 if(n[i].getKind()==kind::AND)
 {
 result = result & (temp1 & temp2);
 Debug("expr-qetest")<<"Left Projection for "<<n[i]<<" is "<<result<<"\n";
 }
 else
 {
 result = result & (temp1|temp2);
 Debug("expr-qetest")<<"Left Projection for "<<n[i]<<" is "<<result<<"\n";
 }
 }
 else
 {
 result = result & evaluateBoolean(n[i]);
 Debug("expr-qetest")<<"Left Projection for "<<n[i]<<" is "<<result<<"\n";
 }
 }
 return result;
 }

 Node QuantifierEliminate::preProcessing2ForRightProjection(Node n) {
 Rational negOne(-1);
 Node test = mkRationalNode(negOne);
 Node returnNode;
 if(n[0].hasBoundVar()) {
 if((n[0].getKind() == kind::MULT) && (n[0][0] == test)) {
 Debug("expr-qetest")<<"n[0] has a -1 as multiply "<<"\n";
 if((n[1]).isConst()) {
 Node temp = NodeManager::currentNM()->mkNode(kind::MULT, test, n[1]);
 temp = Rewriter::rewrite(temp);
 Node temp1 = n[0][1];
 NodeBuilder<> nb(n.getKind());
 nb << temp << temp1;
 returnNode = nb;
 Debug("expr-qetest")<<"Return Node is "<<returnNode<<"\n";
 return returnNode;
 } else if(n[1].getKind() == kind::PLUS) {
 Node temp1 = NodeManager::currentNM()->mkNode(kind::MULT, test,
 n[1][0]);
 Debug("expr-qetest")<<"Before rewriting temp1 "<<temp1<<"\n";
 temp1 = Rewriter::rewrite(temp1);
 Debug("expr-qetest")<<"After rewriting temp1 "<<temp1<<"\n";
 Node temp2 = NodeManager::currentNM()->mkNode(kind::MULT, test,
 n[1][1]);
 Debug("expr-qetest")<<"Before rewriting temp2 "<<temp2<<"\n";
 temp2 = Rewriter::rewrite(temp2);
 Debug("expr-qetest")<<"After rewriting temp2 "<<temp2<<"\n";
 Node temp = NodeManager::currentNM()->mkNode(kind::PLUS, temp1, temp2);
 Debug("expr-qetest")<<"Temp is "<<temp<<"\n";
 Node temp3 = n[0][1];
 Debug("expr-qetest")<<"new n[1] "<<temp3<<"\n";
 NodeBuilder<> nb(n.getKind());
 nb << temp << temp3;
 returnNode = nb;
 Debug("expr-qetest")<<"Return Node is "<<returnNode<<"\n";
 return returnNode;
 }
 }
 else
 {
 returnNode = n;
 return returnNode;
 }
 } else {
 if((n[1].getKind() == kind::MULT) && (n[1][0] == test)) {
 if((n[0]).isConst()) {
 Node temp = NodeManager::currentNM()->mkNode(kind::MULT, test, n[0]);
 temp = Rewriter::rewrite(temp);
 Node temp1 = n[1][1];
 NodeBuilder<> nb(n.getKind());
 nb << temp1 << temp;
 returnNode = nb;
 return returnNode;
 } else if(n[0].getKind() == kind::PLUS) {
 Node temp1 = NodeManager::currentNM()->mkNode(kind::MULT, test,
 n[0][0]);
 temp1 = Rewriter::rewrite(temp1);
 Node temp2 = NodeManager::currentNM()->mkNode(kind::MULT, test,
 n[0][1]);
 temp2 = Rewriter::rewrite(temp2);
 Node temp = NodeManager::currentNM()->mkNode(kind::PLUS, temp1, temp2);
 Node temp3 = n[1][1];
 NodeBuilder<> nb(n.getKind());
 nb << temp3 << temp;
 returnNode = nb;
 Debug("expr-qetest")<<"Return Node is "<<returnNode<<"\n";
 return returnNode;
 }
 }
 else
 {
 returnNode = n;
 return returnNode;
 }
 }
 }

 Node QuantifierEliminate::preProcessingForRightProjection(Node n) {
 Debug("expr-qetest")<<"Node before computing projection "<<n<<"\n";
 Debug("expr-qetest")<<"Number of Children "<<n.getNumChildren()<<"\n";
 std::vector<Node> newNode;
 for(int i=0;i<(int)n.getNumChildren();i++)
 {
 if((n[i].getKind() == kind::AND) || (n[i].getKind() == kind::OR))
 {
 Node left = preProcessing2ForRightProjection(n[i][0]);
 Debug("expr-qetest")<<"Right projection left node "<<left<<"\n";
 Node right = preProcessing2ForRightProjection(n[i][1]);
 Debug("expr-qetest")<<"Right projection right node "<<right<<"\n";
 NodeBuilder<> nb(n[i].getKind());
 nb<<left<<right;
 newNode.push_back(nb);
 }
 else
 {
 Node temp = preProcessing2ForRightProjection(n[i]);
 newNode.push_back(temp);
 }
 }
 Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),newNode);
 Debug("expr-qetest")<<"Right projection returnNode "<<returnNode<<"\n";
 return returnNode;
 }

 Node QuantifierEliminate::evaluateForRightProjection(Node n, Node replacement) {
 std::vector<Node> newNode;
 for(int i = 0; i < (int) n.getNumChildren(); i++) {
 if(n[i][0].hasBoundVar()) {
 Node temp1 = replacement;
 Node temp2 = n[i][1];
 //      Node temp = Rewriter::rewrite(
 //          NodeManager::currentNM()->mkNode(n[i].getKind(), temp1, temp2));
 Node temp = NodeManager::currentNM()->mkNode(n[i].getKind(), temp1, temp2);
 Debug("expr-qetest")<<"Right projection after replacement "<<temp<<"\n";
 newNode.push_back(temp);
 } else {
 Node temp1 = replacement;
 Node temp2 = n[i][0];
 //      Node temp = Rewriter::rewrite(
 //          NodeManager::currentNM()->mkNode(n[i].getKind(), temp2, temp1));
 Node temp = NodeManager::currentNM()->mkNode(n[i].getKind(), temp2, temp1);
 Debug("expr-qetest")<<"Right projection after replacement "<<temp<<"\n";
 newNode.push_back(temp);
 }
 }
 Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(), newNode);
 returnNode = Rewriter::rewrite(returnNode);
 Debug("expr-qetest")<<"Right projection final return node "<<returnNode<<"\n";
 return returnNode;
 }

 Node QuantifierEliminate::computeRightProjection(Node n) {
 Debug("expr-qetest")<<"Node before computing projection "<<n<<"\n";
 Debug("expr-qetest")<<"Number of Children "<<n.getNumChildren()<<"\n";
 Rational posOne(1);
 Node test = mkRationalNode(posOne);
 Node toCompute = preProcessingForRightProjection(n);
 Debug("expr-qetest")<<"Right projection after preprocessing "<<toCompute<<"\n";
 Node replace;
 Node firstAlt;
 Node secondAlt;
 bool truthValue = true;
 for(int i=0;i<(int)toCompute.getNumChildren();i++)
 {
 if((toCompute[i].getKind() == kind::AND) || (toCompute[i].getKind() == kind::OR))
 {
 if(toCompute[i][0][1].hasBoundVar())
 {
 replace = toCompute[i][0][0];
 Debug("expr-qetest")<<"Replace Node "<<replace<<"\n";
 }
 else if(toCompute[i][1][1].hasBoundVar())
 {
 replace = toCompute[i][1][0];
 Debug("expr-qetest")<<"Replace Node "<<replace<<"\n";
 }
 }
 else if(toCompute[i][1].hasBoundVar())
 {
 replace = toCompute[i][0];
 Debug("expr-qetest")<<"Replace Node "<<replace<<"\n";
 }
 }
 if(!replace.isNull())
 {

 firstAlt = replace;
 secondAlt = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::PLUS,test,replace));
 Node result1 = evaluateForRightProjection(n,firstAlt);
 Debug("expr-qetest")<<"Result1 "<<result1<<"\n";
 Node result2 = evaluateForRightProjection(n,secondAlt);
 Debug("expr-qetest")<<"Result2 "<<result2<<"\n";
 }
 else
 {
 truthValue = false;
 return mkBoolNode(truthValue);
 }
 return toCompute;
 }
 */
Node QuantifierEliminate::parseEquation(Node n, Node bv)
{
   Debug("expr-qetest")<<"To rewrite "<<n<<std::endl;
   Debug("expr-qetest")<<"BoundVar "<<bv<<std::endl;
//   if(isConstQE(n))
//   {
//
//   }
   for(Node::kinded_iterator i = n.begin(n.getKind()),
       i_end = n.end(n.getKind());
       i!=i_end;
       ++i)
   {
     Debug("expr-qetest")<<"Inside Iterator "<<*i<<std::endl;
     Node child = *i;
     for(Node::iterator j= child.begin(),end = child.end();j!=end;++j )
     {
       Debug("expr-qetest")<<"Inside inner Iterator "<<*j<<std::endl;
       Debug("expr-qetest")<<"Coefficient "<<returnCoefficientQE(*j)<<std::endl;
     }
   }
   return n;
}
Node QuantifierEliminate::rewriteForSameCoefficients(Node n, Node bv)
{
   Debug("expr-qetest")<<"To rewrite "<<n<<std::endl;
   Debug("expr-qetest")<<"BoundVar "<<bv<<std::endl;
   //
   /*for(Node::kinded_iterator i = n.begin(kind::BOUND_VARIABLE),
                 i_end = n.end(kind::BOUND_VARIABLE);
              i != i_end;
              ++i)
   {
     Debug("expr-qetest")<<"Inside Iterator "<<*i<<std::endl;
   }*/

   Debug("expr-qetest")<<"Number of Children"<<n.getNumChildren()<<std::endl;
   for(int i=0;i<(int)n.getNumChildren();i++)
        {
          Debug("expr-qetest")<<"Child "<<i<<" "<<n[i]<<std::endl;
        }
   if(n.getKind() == kind::NOT)
   {
     n = parseEquation(n[0],bv);
   }
   else
   {
     n = parseEquation(n,bv);
   }




   return n;
}

Node QuantifierEliminate::doRewriting(Node n, std::vector<Node> bv) {
  Debug("expr-qetest")<<"To rewrite"<<n<<std::endl;
  std::vector<Node> temp = bv;
  Node t;
  n = Rewriter::rewrite(n);
  for(int i= 0;i<(int) temp.size();i++)
  {
    t = temp.back();
    n = rewriteForSameCoefficients(n,t);
    temp.pop_back();
  }
  Debug("expr-qetest")<<"After rewriting"<<n<<std::endl;
  return n;
}
bool QuantifierEliminate::computeLeftProjection(Node n, std::vector<Node> bv) {
  return true;
}
Node QuantifierEliminate::computeRightProjection(Node n, std::vector<Node> bv) {
  return n;
}
Node QuantifierEliminate::performCaseAnalysis(Node n, std::vector<Node> bv) {
  Node rewrittenNode = doRewriting(n, bv);
  Debug("expr-qetest")<<"After rewriting "<<rewrittenNode<<"\n";
  bool left = computeLeftProjection(rewrittenNode, bv);
  Debug("expr-qetest")<<"After left projection "<<left<<"\n";
  Node right = computeRightProjection(rewrittenNode, bv);
  Debug("expr-qetest")<<"After right projection "<<right<<"\n";
  //Node finalNode = NodeManager::currentNM()->mkNode(kind::OR, mkBoolNode(left),
  //right);
  Node finalNode = Rewriter::rewrite(right);
  return finalNode;
}

Node QuantifierEliminate::computeProjections(Node n) {
  Node temp1;
  std::vector<Node> temp2;
  Node temp3;
  Node final;
  if((n.getKind() == kind::NOT) || (n.getKind() == kind::FORALL)
      || (n.getKind() == kind::EXISTS)) {
    if(n.getKind() == kind::NOT) {
      if((n[0].getKind() == kind::FORALL) || (n[0].getKind() == kind::EXISTS)) {
        std::vector<Node> multipleBoundVar1;
        if(n[0][0].getNumChildren() > 1) {
          for(int i = 0; i < (int) n[0][0].getNumChildren(); i++) {
             multipleBoundVar1.push_back(n[0][0][i]);
          }
            boundVar.push_back(multipleBoundVar1);
        }
        else
        {
          multipleBoundVar1.push_back(n[0][0][0]);
          boundVar.push_back(multipleBoundVar1);
        }
        args.push_back(n[0][1]);
        return computeProjections(n[0][1].negate());
      } else {
        if(boundVar.size() > 0) {
          while(boundVar.size() > 0) {
            temp1 = args.back();
            temp2 = boundVar.back();
            temp3 = performCaseAnalysis(temp1, temp2);
            temp3 = temp3.negate();
            //args.pop_back();
            boundVar.pop_back();
            while(!args.empty()) {
              args.pop_back();
            }
            args.push_back(temp3);
          }
          final = args.back();
          args.pop_back();
          return final;
        } else {
          final = n.negate();
          return final;
        }
      }
    }
    std::vector<Node> multipleBoundVar2;
    if(n[0].getNumChildren() > 1) {
      for(int i = 0; i < (int) n[0].getNumChildren(); i++) {
        multipleBoundVar2.push_back(n[0][i]);
      }
      boundVar.push_back(multipleBoundVar2);
    }
    else
    {
      multipleBoundVar2.push_back(n[0][0]);
      boundVar.push_back(multipleBoundVar2);
    }
    args.push_back(n[1]);
    return computeProjections(n[1]);
  } else {
    if(boundVar.size() > 0) {
      while(boundVar.size() > 0) {
        temp1 = args.back();
        temp2 = boundVar.back();
        temp3 = performCaseAnalysis(temp1, temp2);
        if(n.getKind() == kind::NOT)
        {
          temp3 = temp3.negate();
        }
        boundVar.pop_back();
        while(!args.empty()) {
          args.pop_back();
        }
        args.push_back(temp3);
      }
      final = args.back();
      args.pop_back();
      return final;
    } else {
      final = n;
      return final;
    }
  }
}

