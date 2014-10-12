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

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;
using namespace CVC4::theory;
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

Node QuantifierEliminate::eliminateImpliesQE(Node body) {
  if(isLiteralQE(body)) {
    return body;
  } else {
    bool childrenChanged = false;
    std::vector<Node> children;
    for(unsigned i = 0; i < body.getNumChildren(); i++) {
      Node c = eliminateImpliesQE(body[i]);
      if(i == 0 && (body.getKind() == kind::IMPLIES)) {
        c = c.negate();
      }
      children.push_back(c);
      childrenChanged = childrenChanged || c != body[i];
    }
    if(body.getKind() == kind::IMPLIES) {
      return NodeManager::currentNM()->mkNode(OR, children);
    } else if(childrenChanged) {
      return NodeManager::currentNM()->mkNode(body.getKind(), children);
    } else {
      return body;
    }
  }
}

Node QuantifierEliminate::convertToPrenexQE(Node body, std::vector<Node>& args,
                                            bool pol) {
  body = replaceForall(body);
  if(body.getKind() == kind::EXISTS) {
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
    Assert( body.getKind()!= kind::FORALL );
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

Node QuantifierEliminate::convertToNNFQE(Node body) {

  if(body.getKind() == kind::NOT) {
    if(body[0].getKind() == kind::NOT) {
      //  Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][0].getKind() << "\n";
      return convertToNNFQE(body[0][0]);
    } else if(isLiteralQE(body[0])) {
      //  Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getKind() << "\n";
      return body;
    } else {
      std::vector<CVC4::Node> children;
      Kind k = body[0].getKind();
      if(body[0].getKind() == kind::OR || body[0].getKind() == kind::AND) {
        for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
          children.push_back(convertToNNFQE(body[0][i].notNode()));
        }
        k = body[0].getKind() == kind::AND ? kind::OR : kind::AND;
        Debug("expr-qetest")<<"New kind after negation "<<k<<"\n";
      }
      else {
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return NodeManager::currentNM()->mkNode(k, children);
    }
  } else if(isLiteralQE(body)) {
    return body;
  } else {
    std::vector<CVC4::Node> children;
    bool childrenChanged = false;
    for(int i = 0; i < (int) body.getNumChildren(); i++) {
      Node nc = convertToNNFQE(body[i]);
      children.push_back(nc);
      childrenChanged = childrenChanged || nc != body[i];
    }
    if(childrenChanged) {
      return NodeManager::currentNM()->mkNode(body.getKind(), children);
    } else {
      return body;
    }
  }
}
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
Node QuantifierEliminate::replaceForall(Node n) {
  if(n.getKind() == kind::FORALL) {
    std::vector<Node> children;
    children.push_back(n[0]);
    children.push_back(n[1].notNode());
    if(n.getNumChildren()) {
      children.push_back(n[2]);
    }
    n = NodeManager::currentNM()->mkNode(kind::EXISTS, children);
    n = n.notNode();
  }
  return n;
}

Node QuantifierEliminate::doRewriting(Node n, Node boundVar) {
  return n;
}
bool QuantifierEliminate::computeLeftProjection(Node n, Node boundVar) {
  return true;
}
Node QuantifierEliminate::computeRightProjection(Node n, Node boundVar) {
  return n;
}
Node QuantifierEliminate::performCaseAnalysis(Node n, Node boundVar) {
  Node rewrittenNode = doRewriting(n, boundVar);
  Debug("expr-qetest")<<"After rewriting "<<rewrittenNode<<"\n";
  bool left = computeLeftProjection(rewrittenNode, boundVar);
  Debug("expr-qetest")<<"After left projection "<<left<<"\n";
  Node right = computeRightProjection(rewrittenNode, boundVar);
  Debug("expr-qetest")<<"After right projection "<<right<<"\n";
  //Node finalNode = NodeManager::currentNM()->mkNode(kind::OR, mkBoolNode(left),
                                                    //right);
  Node finalNode = Rewriter::rewrite(right);
  return finalNode;
}

Node QuantifierEliminate::doPreprocessing(Expr ex) {
  Node temp_in = NodeTemplate<true>(ex);
  Node rewrittenNode = Rewriter::rewrite(temp_in);
  return rewrittenNode;
  /*Debug("expr-qetest") << "------- Inside doProcessing Method ------" << "\n";
   Node in;
   if(temp_in.getKind() == kind::NOT) {
   in = temp_in[0];
   } else {
   in = temp_in;
   }
   // in = replaceForall(in);
   Kind initialKind = in.getKind();
   if(initialKind == kind::EXISTS || initialKind == kind::FORALL) {
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
   Node nnfNode = convertToNNFQE(n);
   Debug("expr-qetest") << "After nnf "<< nnfNode << "\n";
   if(nnfNode.isNull()) {
   Debug("expr-qetest") << "Node rewrittenNode is null in doPreprocessing after rewriting " << "\n";
   }
   Node rewrittenNode = Rewriter::rewrite(nnfNode);
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
   defs << NodeManager::currentNM()->mkNode(initialKind, children);
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

   }*/
}

Node QuantifierEliminate::computeProjections(Node n,std::vector<Node> boundVar,std::vector<Node> args) {
  Debug("expr-qetest") << "------- Inside Compute Projection Method ------" << "\n";
  Debug("expr-qetest") << n << "\n";
  Node result;
  Node temp;
  Debug("expr-qetest") << "boundVar size" << boundVar.size()<<"\n";
  Debug("expr-qetest") << "args size" << args.size()<<"\n";
  if(n.getKind() == kind::NOT)
  {
    temp = n[0];
  }
  else
  {
    temp = n;
  }
  if(temp.getKind()==kind::EXISTS || temp.getKind() == kind::FORALL || (!boundVar.empty() && !args.empty()))
  {
    if(temp.getKind()==kind::EXISTS || temp.getKind() == kind::FORALL)
    {
      boundVar.push_back(temp[0]);
      Debug("expr-qetest")<<"Bound Variable "<<boundVar.back()<<"\n";
      args.push_back(temp[1]);
      Debug("expr-qetest")<<"Argument "<<args.back()<<"\n";
    }
    Node n1 = args.back();
    if(n1.getKind() == kind::EXISTS || n1.getKind() == kind::FORALL || n1.getKind() == kind::NOT)
    {
      return computeProjections(n1,boundVar,args);
    }
    else
    {
      while(!boundVar.empty() && !args.empty())
      {
        Node varToElim = boundVar.back();
        Node finalNode = performCaseAnalysis(n1,varToElim);
        args.pop_back();
        boundVar.pop_back();
        if(n1.getKind() == kind::NOT)
        {
          n1 = finalNode.notNode();
        }
        else
        {
          n1 = finalNode;
        }
        result = n1;
      }
    }
    if(n.getKind() == kind::NOT)
    {
      result = result.notNode();
      return result;
    }
    else
    {
      return result;
    }
  }
  else
  {
    return n;
  }
}

