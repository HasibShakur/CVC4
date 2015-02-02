//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include<numeric>
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
std::vector<Container> QuantifierEliminate::container;
Integer QuantifierEliminate::lcmValue;
bool QuantifierEliminate::negationDone;
Integer QuantifierEliminate::negateCount;

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
/* Node QuantifierEliminate::preProcessing2ForRightProjection(Node n) {
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
/*Node QuantifierEliminate::substitutioForQE(Node original,Node toReplace,Node replacement)
 {
 std::vector<Node> nodes;
 Kind k = original.getKind();
 for(Node::iterator a = original.begin(),a_end = original.end();
 a != a_end;
 ++a)
 {
 Node b = *a;
 nodes.push_back(b);
 }
 Node reconstructed = NodeManager::currentNM()->mkNode(k,nodes);
 if(reconstructed != original)
 {
 Debug("expr-qetest") <<"Not same "<<original<<" "<<reconstructed<<std::endl;
 }
 }*/

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
bool QuantifierEliminate::isConstQE(Node n) {
  if(n.isConst())
    return true;
  else
    return false;
}
bool QuantifierEliminate::isVarQE(Node n) {
  if(n.isVar() && !isVarWithCoefficientsQE(n) && !isEquationQE(n))
    return true;
  else
    return false;
}
bool QuantifierEliminate::isVarWithCoefficientsQE(Node n) {
  if(n.getKind() == kind::MULT && isConstQE(n[0]) && isVarQE(n[1])) {
    return true;
  } else {
    return false;
  }
}

bool QuantifierEliminate::isEquationQE(Node n) {
  if((isRelationalOperatorTypeQE(n.getKind())) || (n.getKind() == kind::PLUS)
      || (n.getKind() == kind::MINUS))
    return true;
  else
    return false;
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
      } else {
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

Integer QuantifierEliminate::getIntegerFromNode(Node n) {
  Constant c = Constant::mkConstant(n);
  Rational r = c.getValue();
  Integer i = r.getNumerator();
  return i;
}
Node QuantifierEliminate::fromIntegerToNodeQE(Integer n) {
  Rational r(n);
  Constant c = Constant::mkConstant(r);
  return c.getNode();
}

Node QuantifierEliminate::getShiftedExpression(Node n, Node bv) {
  std::vector<Node> shiftedNodes;
  Node shift;
  for(Node::iterator l = n.begin(), l_end = n.end(); l != l_end; ++l) {
    Node childL = *l;
    if(childL.hasBoundVar() && containsSameBoundVar(childL, bv)) {
    } else {
      if(isVarQE(childL)) {
        Node convertChildL = NodeManager::currentNM()->mkNode(
            kind::MULT, fromIntegerToNodeQE(-1), childL);
        shiftedNodes.push_back(convertChildL);
      } else if(isVarWithCoefficientsQE(childL)) {
        Integer neg = getIntegerFromNode(childL[0]) * -1;
        TNode tn1 = childL[0];
        TNode tn2 = fromIntegerToNodeQE(neg);
        childL = childL.substitute(tn1, tn2);
        shiftedNodes.push_back(childL);
      } else {
        Integer neg = getIntegerFromNode(childL) * -1;
        Node convertChildL = fromIntegerToNodeQE(neg);
        shiftedNodes.push_back(convertChildL);
      }
    }
  }
  if(shiftedNodes.size() > 1) {
    shift = NodeManager::currentNM()->mkNode(kind::PLUS, shiftedNodes);
    return shift;
  } else {
    shift = shiftedNodes.back();
    shiftedNodes.pop_back();
    return shift;
  }
}
Node QuantifierEliminate::separateBoundVarExpression(Node n, Node bv) {
  Node toReturn;
  for(Node::iterator inner = n.begin(), inner_end = n.end(); inner != inner_end;
      ++inner) {
    Node innerChild = *inner;
    if(isConstQE(innerChild)) {
    } else {
      if(innerChild.hasBoundVar() && containsSameBoundVar(innerChild, bv)) {
        toReturn = innerChild;
        break;
      } else {
      }
    }

  }
  return toReturn;
}

void QuantifierEliminate::parseCoefficientQE(Node n, QuantifierEliminate q) {
  Node temp;
  if(n.getKind() == kind::NOT) {
    temp = n[0];
  } else {
    temp = n;
  }
  if(isConstQE(temp)) {
    Integer n = getIntegerFromNode(temp);
    Container c(temp, n);
    container.push_back(c);
  } else if(isVarQE(temp)) {
    Constant one = Constant::mkOne();
    Integer n = getIntegerFromNode(one.getNode());
    Container c(temp, n);
    container.push_back(c);
  } else if(isVarWithCoefficientsQE(temp)) {
    Integer n = getIntegerFromNode(temp[0]);
    Container c(temp[1], n);
    container.push_back(c);
  } else {
    for(Node::iterator i = temp.begin(), end = temp.end(); i != end; ++i) {
      Node child = *i;
      if(isVarWithCoefficientsQE(child)) {
        Integer n = getIntegerFromNode(child[0]);
        Container c(child[1], n);
        container.push_back(c);
      } else if(isConstQE(child)) {
        Integer n = getIntegerFromNode(child);
        Container c(child, n);
        container.push_back(c);
      } else if(isVarQE(child)) {
        Constant one = Constant::mkOne();
        Integer n = getIntegerFromNode(one.getNode());
        Container c(child, n);
        container.push_back(c);
      } else {
        for(Node::iterator j = child.begin(), end = child.end(); j != end;
            ++j) {
          Node inner = *j;
          if(isConstQE(inner)) {
            Integer n = getIntegerFromNode(inner);
            Container c(inner, n);
            container.push_back(c);
          } else if(isVarQE(inner)) {
            Constant one = Constant::mkOne();
            Integer n = getIntegerFromNode(one.getNode());
            Container c(inner, n);
            container.push_back(c);
          } else {
            Integer n = getIntegerFromNode(inner[0]);
            Container c(inner[1], n);
            container.push_back(c);
          }
        }
      }

    }
  }
}
Integer QuantifierEliminate::lcmQE(Integer a, Integer b) {
  return a.lcm(b);
}
Integer QuantifierEliminate::calculateLCMofCoeff(std::vector<Integer> coeffs) {
  Integer one = 1;
  Integer lcmResult = std::accumulate(coeffs.begin(), coeffs.end(), one, lcmQE);
  return lcmResult;
}
bool QuantifierEliminate::containsSameBoundVar(Node n, Node bv) {
  if(isVarQE(n)) {
    if(n == bv) {
      return true;
    } else {
      return false;
    }
  } else if(isVarWithCoefficientsQE(n)) {
    if(n[1] == bv) {
      return true;
    } else {
      return false;
    }
  } else {
    for(Node::iterator i = n.begin(), end = n.end(); i != end; ++i) {
      Node child = *i;
      if(isConstQE(child)) {
      } else if(isVarWithCoefficientsQE(child)) {
        if(child[1] == bv) {
          return true;
        } else {
        }
      } else if(isVarQE(child)) {
        if(child == bv) {
          return true;
        } else {
        }
      } else {
        for(Node::iterator i_inner = child.begin(), i_end = child.end();
            i_inner != i_end; ++i_inner) {
          Node child_inner = *i_inner;
          if(isVarQE(child_inner)) {
            if(child_inner == bv) {
              return true;
            } else {
            }
          } else if(isVarWithCoefficientsQE(child_inner)) {
            if(child_inner[1] == bv) {
              return true;
            } else {
            }
          } else {
          }
        }
      }
    }
    return false;
  }

}
Integer QuantifierEliminate::getLcmResult(Node t, Node bv,
                                          QuantifierEliminate q) {
  std::vector<Integer> boundVarCoeff;
  for(Node::kinded_iterator i = t.begin(t.getKind()), i_end = t.end(
      t.getKind()); i != i_end; ++i) {
    Node child = *i;
    parseCoefficientQE(child, q);
  }
  std::vector<Container> tempContainer = container;
  for(int i = 0; i < (int) tempContainer.size(); i++) {
    Debug("expr-qetest")<<"Variable "<<tempContainer[i].getVariable()<<" Coefficient "<<tempContainer[i].getCoefficient()<<std::endl;
  }
  Integer coeff = 1;
  for(int i = 0; i < (int) tempContainer.size(); i++) {
    if(tempContainer[i].getVariable() == bv) {
      boundVarCoeff.push_back(tempContainer[i].getCoefficient());
    }
  }
  Integer lcmResult = calculateLCMofCoeff(boundVarCoeff);
  Debug("expr-qetest")<<"lcmResult in getLcmResult "<<lcmResult<<std::endl;
  return lcmResult;
}

Node QuantifierEliminate::parseEquation(Node t, Node bv,
                                        QuantifierEliminate q) {
  std::vector<ExpressionContainer> temExpContainer = q.getExpContainer(q);
  Integer coeff = 1;
  Node n;
  if(t.getKind() == kind::NOT) {
    n = t[0];
  } else {
    n = t;
  }
  Integer lcmResult = getLcmResult(n, bv, q);
  lcmValue = lcmResult;
  Debug("expr-qetest")<<"lcm "<<lcmResult<<std::endl;
  Debug("expr-qetest")<<"container size "<<container.size()<<std::endl;
  std::vector<Container> tempContainer = container;
  for(int i = 0; i < (int) tempContainer.size(); i++) {
    if(tempContainer[i].getVariable() == bv) {
      coeff = tempContainer[i].getCoefficient();
    }
  }
  Debug("expr-qetest")<<"Coeff "<<coeff<<std::endl;
  Integer multiple = lcmResult.euclidianDivideQuotient(coeff.abs());
  Debug("expr-qetest")<<"multiple "<<multiple<<std::endl;
  while(!container.empty()) {
    container.pop_back();
  }
  if(lcmResult == 1 || multiple == 1) {
    Debug("expr-qetest")<<"After lcm operation expression "<<t<<std::endl;
    return t;
  }
  else
  {
    Node n;
    if(t.getKind() == kind::NOT)
    {
      n = t[0];
    }
    else
    {
      n = t;
    }
    Kind k = n.getKind();
    Integer multiplier = 1;
    bool singleExp = false;
    for(Node::iterator i = n.begin(),i_end = n.end();
    i!=i_end;
    ++i)
    {
      Node child = *i;
      multiplier = 1;
      Node tempChild;
      if(child.getKind() == kind::NOT)
      {
        tempChild = child[0];
      }
      else
      {
        tempChild = child;
      }
      if(child.hasBoundVar())
      {
        if(isConstQE(child))
        {}
        else if(isVarQE(child))
        {
          singleExp = true;
          multiplier = (multiplier*lcmResult).abs();
          Debug("expr-qetest") <<"multiplier "<<multiplier<<std::endl;
        }
        else if(isVarWithCoefficientsQE(child))
        {
          singleExp = true;
          Integer x = getIntegerFromNode(child[0]).abs();
          multiplier = lcmResult.euclidianDivideQuotient(x);
          Debug("expr-qetest") <<"multiplier "<<multiplier<<std::endl;
        }
        else
        {
          for(Node::iterator j = tempChild.begin(),j_end = tempChild.end();
          j != j_end;
          ++j )
          {
            Node child1 = *j;
            Debug("expr-qetest") <<"child 1 "<<child1<<std::endl;
            if(child1.hasBoundVar() && containsSameBoundVar(child1,bv))
            {
              if(isConstQE(child1)) {}
              else if(isVarQE(child1))
              {
                multiplier = (multiplier*lcmResult).abs();
                Debug("expr-qetest") <<"multiplier "<<multiplier<<std::endl;
              }
              else if(isVarWithCoefficientsQE(child1))
              {
                Integer x = getIntegerFromNode(child1[0]).abs();
                multiplier = lcmResult.euclidianDivideQuotient(x);
                Debug("expr-qetest") <<"multiplier "<<multiplier<<std::endl;
              }
              else
              {
                for(Node::iterator k = child1.begin(),k_end = child1.end();
                k != k_end;
                ++k)
                {
                  Node child2 = *k;
                  if(child2.hasBoundVar() && containsSameBoundVar(child2,bv))
                  {
                    if(isVarQE(child2))
                    {
                      multiplier = (multiplier*lcmResult).abs();
                    }
                    else if(isVarWithCoefficientsQE(child2))
                    {
                      Integer x = getIntegerFromNode(child2[0]).abs();
                      multiplier = lcmResult.euclidianDivideQuotient(x);
                    }
                    else
                    {}
                  }
                  else
                  {}
                }
              }
            }
            else
            {}
          }
        }
        if(!singleExp)
        {
          ExpressionContainer e(child,multiplier);
          temExpContainer.push_back(e);
        }
      }
      else
      {}
    }
    if(singleExp)
    {
      ExpressionContainer e(n,multiplier);
      temExpContainer.push_back(e);
    }
    for(int i= 0;i<(int)temExpContainer.size();i++)
    {
      Debug("expr-qetest")<<"Expression "<<temExpContainer[i].getExpression()<<" multiplier "<<temExpContainer[i].getMultiplier()<<std::endl;
    }
    std::vector<Node> finalExpr;
    for(int i=0;i<(int)temExpContainer.size();i++)
    {
      Node child = temExpContainer[i].getExpression();
      Integer multiple = temExpContainer[i].getMultiplier();
      std::vector<Node> child_expr;
      Node tempChild;
      if(child.getKind() == kind::NOT)
      {
        tempChild = child[0];
      }
      else
      {
        tempChild = child;
      }
      Debug("expr-qetest")<<"tempChild "<<tempChild<<std::endl;
      for(Node::iterator p = tempChild.begin(),pEnd = tempChild.end();
      p != pEnd;
      ++p)
      {
        Node child2 = *p;
        if(isConstQE(child2))
        {
          Debug("expr-qetest")<<"constant "<<child2<<std::endl;
          Integer x = getIntegerFromNode(child2) * multiple;
          child_expr.push_back(fromIntegerToNodeQE(x));
        }
        else if(isVarQE(child2))
        {
          Debug("expr-qetest")<<"var "<<child2<<std::endl;
          Node temp = NodeManager::currentNM()->mkNode(kind::MULT,child2,fromIntegerToNodeQE(multiple));
          child_expr.push_back(temp);
        }
        else if(isVarWithCoefficientsQE(child2))
        {
          Debug("expr-qetest")<<"var with coeff "<<child2<<std::endl;
          Integer x = getIntegerFromNode(child2[0]) * multiple;
          Node temp = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(x),child2[1]);
          child_expr.push_back(temp);
        }
        else
        {
          std::vector<Node> right;
          Kind k_child = child2.getKind();
          for(Node::iterator j = child2.begin(),j_end = child2.end();
          j!=j_end;
          ++j)
          {
            Node child3 = *j;
            if(isConstQE(child3))
            {
              Debug("expr-qetest")<<"inner constant "<<child3<<std::endl;
              Integer x = getIntegerFromNode(child3) * multiple;
              Node c_temp = fromIntegerToNodeQE(x);
              right.push_back(c_temp);
            }
            else if(isVarQE(child3))
            {
              Debug("expr-qetest")<<"inner var "<<child3<<std::endl;
              Node var = child3;
              Node coeff = fromIntegerToNodeQE(multiple);
              Node c_temp = NodeManager::currentNM()->mkNode(kind::MULT,coeff,var);
              right.push_back(c_temp);

            }
            else
            {
              Debug("expr-qetest")<<"inner var with coefficients "<<child3<<std::endl;
              Node var = child3[1];
              Integer b = getIntegerFromNode(child3[0]);
              b = b*multiple;
              Node coeff = fromIntegerToNodeQE(b);
              Node c_temp = NodeManager::currentNM()->mkNode(kind::MULT,coeff,var);
              right.push_back(c_temp);
            }
          }
          Node temp = NodeManager::currentNM()->mkNode(k_child,right);
          Debug("expr-qetest")<<"temp "<<temp<<std::endl;
          child_expr.push_back(temp);
        }
      }
      Node child_temp = NodeManager::currentNM()->mkNode(tempChild.getKind(),child_expr);
      Debug("expr-qetest")<<"child_temp "<<child_temp<<std::endl;
      if(child.getKind() == kind::NOT)
      {
        child_temp = child_temp.negate();
      }
      finalExpr.push_back(child_temp);
    }
//    Divisible
//    finalExpr.push_back(divisible);
    Node finalNode = NodeManager::currentNM()->mkNode(k,finalExpr);
    if(t.getKind() == kind::NOT)
    {
      Debug("expr-qetest")<<"After lcm operation expression "<<finalNode.negate()<<std::endl;
      return finalNode.negate();
    }
    else
    {
      Debug("expr-qetest")<<"After lcm operation expression "<<finalNode<<std::endl;
      return finalNode;
    }
  }
}
Node QuantifierEliminate::replaceGTQE(Node n, Node bv) {
  Node returnNode;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      } else {
        Node shiftedNodes = getShiftedExpression(left, bv);
        left = separateBoundVarExpression(left, bv);
        if(!shiftedNodes.isNull()) {
          right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                                   shiftedNodes);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      }
    } else {
      if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      } else {
        Node shiftedNodes = getShiftedExpression(right, bv);
        right = separateBoundVarExpression(right, bv);
        if(!shiftedNodes.isNull()) {
          left = NodeManager::currentNM()->mkNode(kind::PLUS, left,
                                                  shiftedNodes);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
        return returnNode;
      }
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceGEQQE(Node n, Node bv) {
  Node returnNode;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft;
    Node tempRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS
          || tempLeft.getKind() == kind::MINUS) {
        Node shiftedFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {

          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x - 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(-1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x - 1;
            tempRight = fromIntegerToNodeQE(x);
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(-1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }
      } else {
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x - 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x - 1;
            tempRight = fromIntegerToNodeQE(x);
          } else {

            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }
      }
    } else {
      tempLeft = left;
      tempRight = right;
      if(tempRight.getKind() == kind::PLUS
          || tempRight.getKind() == kind::MINUS) {
        Node shiftedFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {

          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x + 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x + 1;
            tempRight = fromIntegerToNodeQE(x);
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }

      } else {
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x + 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempRight = fromIntegerToNodeQE(x);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }

          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                        tempLeft);
        }
      }
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    if(isConstQE(right)) {
      Integer x = getIntegerFromNode(right);
      x = x - 1;
      right = fromIntegerToNodeQE(x);
    } else {
      right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                               fromIntegerToNodeQE(-1));
      right = Rewriter::rewrite(right);
    }
    returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
  }
  return returnNode;
}
Node QuantifierEliminate::replaceLEQQE(Node n, Node bv) {
  Node returnNode;
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft;
    Node tempRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS
          || tempLeft.getKind() == kind::MINUS) {
        Node shiftedFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, shiftedFromLeft, fromIntegerToNodeQE(x));
            } else {
              tempRight = fromIntegerToNodeQE(x);
            }

          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }

      } else {
        tempLeft = left;
        tempRight = right;
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            tempRight = fromIntegerToNodeQE(x);
          }

          else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }
    } else {
      tempLeft = left;
      tempRight = right;
      if(tempRight.getKind() == kind::PLUS
          || tempRight.getKind() == kind::MINUS) {
        Node shiftedFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          }
        }
      } else {
        tempLeft = left;
        tempRight = right;
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
          }

          else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    if(isConstQE(right)) {
      Integer x = getIntegerFromNode(right);
      x = x + 1;
      right = fromIntegerToNodeQE(x);
    } else {
      right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                               fromIntegerToNodeQE(1));
      right = Rewriter::rewrite(right);
    }
    returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
  }
  return returnNode;
}
Node QuantifierEliminate::replaceEQUALQE(Node n, Node bv) {
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node finalLeft;
    Node finalRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      if(right.getKind() == kind::PLUS || right.getKind() == kind::MINUS) {
        Node tempLeft = left;
        Node tempRight = right;
        bool flag = false;
        Node shiftFromLeft;
        if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
          tempLeft = left;
        } else {
          shiftFromLeft = getShiftedExpression(tempLeft, bv);
          tempLeft = separateBoundVarExpression(tempLeft, bv);
        }
        for(Node::iterator j = tempRight.begin(), j_end = tempRight.end();
            j != j_end; ++j) {
          Node child = *j;
          if(isConstQE(child)) {
            Integer x = getIntegerFromNode(child);
            x = x + 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = child;
            TNode tn2 = change;
            tempRight = tempRight.substitute(tn1, tn2);
            flag = true;
            break;
          } else {
          }
        }
        if(!flag) {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         fromIntegerToNodeQE(1),
                                                         shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }

        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempRight = right;
        bool flag1 = false;
        for(Node::iterator j = tempRight.begin(), j_end = tempRight.end();
            j != j_end; ++j) {
          Node child = *j;
          if(isConstQE(child)) {
            Integer x = getIntegerFromNode(child);
            x = x - 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = child;
            TNode tn2 = change;
            tempRight = tempRight.substitute(tn1, tn2);
            flag1 = true;
            break;
          } else {
          }
        }
        if(!flag1) {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1), shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }

        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        }

        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      } else {
        Node tempLeft = left;
        Node tempRight = right;
        Node shiftFromLeft;
        if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
          tempLeft = left;
        } else {
          shiftFromLeft = getShiftedExpression(tempLeft, bv);
          tempLeft = separateBoundVarExpression(tempLeft, bv);
        }
        if(isConstQE(tempRight)) {
          Integer x = getIntegerFromNode(tempRight);
          x = x + 1;
          TNode tn1 = tempRight;
          TNode tn2 = fromIntegerToNodeQE(x);
          tempRight = tempRight.substitute(tn1, tn2);
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         fromIntegerToNodeQE(1),
                                                         shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempRight = right;
        if(isConstQE(right)) {
          Integer x = getIntegerFromNode(tempRight);
          x = x - 1;
          TNode tn1 = tempRight;
          TNode tn2 = fromIntegerToNodeQE(x);
          tempRight = tempRight.substitute(tn1, tn2);
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         shiftFromLeft);
          }
        } else {
          if(!shiftFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1), shiftFromLeft);
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }

        }
        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      }
    } else {
      if(right.getKind() == kind::PLUS || right.getKind() == kind::MINUS) {
        Node tempLeft = left;
        Node tempRight = right;
        bool flag = false;
        Node shiftFromRight;
        if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
          tempRight = right;
        } else {
          shiftFromRight = getShiftedExpression(tempRight, bv);
          tempRight = separateBoundVarExpression(tempRight, bv);
        }
        for(Node::iterator j = tempLeft.begin(), j_end = tempLeft.end();
            j != j_end; ++j) {
          Node childJ = *j;
          if(isConstQE(childJ)) {
            Integer x = getIntegerFromNode(childJ);
            x = x - 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = childJ;
            TNode tn2 = change;
            tempLeft = tempLeft.substitute(tn1, tn2);
            flag = true;
            break;
          } else {
          }
        }
        if(!flag) {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(-1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempLeft = left;
        bool flag1 = false;
        for(Node::iterator j = tempLeft.begin(), j_end = tempLeft.end();
            j != j_end; ++j) {
          Node child = *j;
          if(isConstQE(child)) {
            Integer x = getIntegerFromNode(child);
            x = x + 1;
            Node change = fromIntegerToNodeQE(x);
            TNode tn1 = child;
            TNode tn2 = change;
            tempLeft = tempLeft.substitute(tn1, tn2);
            flag1 = true;
            break;
          } else {
          }
        }
        if(!flag1) {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        }
        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      } else {
        Node tempLeft = left;
        Node tempRight = right;
        Node shiftFromRight;
        if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
          tempRight = right;
        } else {
          shiftFromRight = getShiftedExpression(tempRight, bv);
          tempRight = separateBoundVarExpression(tempRight, bv);
        }
        if(isConstQE(tempLeft)) {
          Integer x = getIntegerFromNode(tempLeft);
          x = x - 1;
          Node change = fromIntegerToNodeQE(x);
          TNode tn1 = tempLeft;
          TNode tn2 = change;
          tempLeft = tempLeft.substitute(tn1, tn2);
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(-1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
        }
        finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                     tempRight);
        tempLeft = left;
        if(isConstQE(tempLeft)) {
          Integer x = getIntegerFromNode(tempLeft);
          x = x + 1;
          Node change = fromIntegerToNodeQE(x);
          TNode tn1 = tempLeft;
          TNode tn2 = change;
          tempLeft = tempLeft.substitute(tn1, tn2);
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftFromRight);
          }
        } else {
          if(!shiftFromRight.isNull()) {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1),
                                                        shiftFromRight);
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
        }
        finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
        Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                           finalRight);
        return returnNode;
      }

    }
  } else {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft = left;
    Node tempRight = right;
    Node returnNode;
    if(isConstQE(tempRight)) {
      Integer x = getIntegerFromNode(tempRight) + 1;
      tempRight = fromIntegerToNodeQE(x);
    } else {
      tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                   fromIntegerToNodeQE(1));
      tempRight = Rewriter::rewrite(tempRight);
    }
    Node finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                      tempRight);
    tempRight = right;
    if(isConstQE(tempLeft)) {
      Integer x = getIntegerFromNode(tempLeft) + 1;
      tempLeft = fromIntegerToNodeQE(x);
    } else {
      tempLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                  fromIntegerToNodeQE(1));
      tempLeft = Rewriter::rewrite(tempLeft);
    }
    Node finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                       tempLeft);
    returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
                                                  finalRight);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceLTQE(Node n, Node bv) {
  if(n.hasBoundVar() && containsSameBoundVar(n, bv)) {
    Node left = n[0];
    Node right = n[1];
    Node shiftExpr;
    Node returnNode;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      } else {
        shiftExpr = getShiftedExpression(left, bv);
        left = separateBoundVarExpression(left, bv);
        if(!shiftExpr.isNull()) {
          right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                                   shiftExpr);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      }
    } else {
      if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      } else {
        shiftExpr = getShiftedExpression(right, bv);
        right = separateBoundVarExpression(right, bv);
        if(!shiftExpr.isNull()) {
          left = NodeManager::currentNM()->mkNode(kind::PLUS, left, shiftExpr);
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
      }
    }
    return returnNode;

  } else {
    Node left = n[0];
    Node right = n[1];
    Node returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceNegateLTQE(Node n, Node bv) {
  n = replaceGEQQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateLEQQE(Node n, Node bv) {
  n = replaceGTQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateGTQE(Node n, Node bv) {
  if(n[0].hasBoundVar() && containsSameBoundVar(n[0], bv)) {
    Node left = n[0][0];
    Node right = n[0][1];
    Node tempLeft;
    Node tempRight;
    Node returnNode;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS
          || tempLeft.getKind() == kind::MINUS) {
        Node shiftedFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,
                                                           tempRight,
                                                           shiftedFromLeft);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, shiftedFromLeft, fromIntegerToNodeQE(x));
            } else {
              tempRight = fromIntegerToNodeQE(x);
            }

          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, shiftedFromLeft,
                  fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }

      } else {
        tempLeft = left;
        tempRight = right;
        if(tempRight.getKind() == kind::PLUS
            || tempRight.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator rightBegin = tempRight.begin(), rightEnd =
              tempRight.end(); rightBegin != rightEnd; ++rightBegin) {
            Node childR = *rightBegin;
            if(isConstQE(childR)) {
              Integer x = getIntegerFromNode(childR);
              x = x + 1;
              TNode tn1 = childR;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempRight = tempRight.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempRight)) {
            Integer x = getIntegerFromNode(tempRight);
            x = x + 1;
            tempRight = fromIntegerToNodeQE(x);
          }

          else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }
    } else {
      tempLeft = left;
      tempRight = right;
      if(tempRight.getKind() == kind::PLUS
          || tempRight.getKind() == kind::MINUS) {
        Node shiftedFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                          shiftedFromRight);
            }
          } else {
            if(!shiftedFromRight.isNull()) {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, shiftedFromRight,
                  fromIntegerToNodeQE(-1));
            } else {
              tempLeft = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
            }
          }
        }
      } else {
        tempLeft = left;
        tempRight = right;
        if(tempLeft.getKind() == kind::PLUS
            || tempLeft.getKind() == kind::MINUS) {
          bool flag = false;
          for(Node::iterator leftBegin = tempLeft.begin(), leftEnd =
              tempLeft.end(); leftBegin != leftEnd; ++leftBegin) {
            Node childL = *leftBegin;
            if(isConstQE(childL)) {
              Integer x = getIntegerFromNode(childL);
              x = x - 1;
              TNode tn1 = childL;
              TNode tn2 = fromIntegerToNodeQE(x);
              tempLeft = tempLeft.substitute(tn1, tn2);
              flag = true;
              break;
            }
          }
          if(!flag) {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        } else {
          if(isConstQE(tempLeft)) {
            Integer x = getIntegerFromNode(tempLeft);
            x = x - 1;
            tempLeft = fromIntegerToNodeQE(x);
          }

          else {
            tempLeft = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempLeft, fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
        }
      }

    }
    return returnNode;

  } else {
    Node left = n[0][0];
    Node right = n[0][1];
    if(isConstQE(right)) {
      Integer x = getIntegerFromNode(right) + 1;
      right = fromIntegerToNodeQE(x);
    } else {
      right = NodeManager::currentNM()->mkNode(kind::PLUS, right,
                                               fromIntegerToNodeQE(1));
      right = Rewriter::rewrite(right);
    }
    Node returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
    return returnNode;
  }
}
Node QuantifierEliminate::replaceNegateGEQQE(Node n, Node bv) {
  n = replaceLTQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateEQUALQE(Node n, Node bv) {
  if(n[0].hasBoundVar() && containsSameBoundVar(n[0], bv)) {
    Node left = n[0][0];
    Node right = n[0][1];
    Node finalLeft;
    Node finalRight;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      Node tempLeft = left;
      Node tempRight = right;
      Node shiftFromLeft;
      if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
        tempLeft = left;
      } else {
        shiftFromLeft = getShiftedExpression(tempLeft, bv);
        tempLeft = separateBoundVarExpression(tempLeft, bv);
      }
      if(!shiftFromLeft.isNull()) {
        tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                     shiftFromLeft);
      }
      finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                   tempRight);
      tempRight = right;
      if(!shiftFromLeft.isNull()) {
        tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                     shiftFromLeft);
      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                    tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                         finalRight);
      return returnNode;
    } else {
      //right has boundvar bv
      Node tempLeft = left;
      Node tempRight = right;
      Node shiftFromRight;
      if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
        tempRight = right;
      } else {
        shiftFromRight = getShiftedExpression(tempRight, bv);
        tempRight = separateBoundVarExpression(tempRight, bv);
      }
      if(!shiftFromRight.isNull()) {
        tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                    shiftFromRight);
      }
      finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                   tempRight);
      tempLeft = left;
      if(!shiftFromRight.isNull()) {
        tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                    shiftFromRight);
      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                    tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                         finalRight);
      return returnNode;
    }
  } else {
    Node left = n[0];
    Node right = n[1];
    Node tempLeft = left;
    Node tempRight = right;
    Node returnNode;
    Node finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                      tempRight);
    Node finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                       tempLeft);
    returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                  finalRight);
    return returnNode;
  }

}
Node QuantifierEliminate::replaceRelationOperatorQE(Node n, Node bv) {
  Node replaceNode;
  if(n.getKind() == kind::NOT) {
    Node temp = n[0];
    if(temp.getKind() == kind::LT) {
      replaceNode = replaceNegateLTQE(n, bv);
    } else if(temp.getKind() == kind::LEQ) {
      replaceNode = replaceNegateLEQQE(n, bv);
    } else if(temp.getKind() == kind::GT) {
      replaceNode = replaceNegateGTQE(n, bv);
    } else if(temp.getKind() == kind::GEQ) {
      replaceNode = replaceNegateGEQQE(n, bv);
    } else if(temp.getKind() == kind::EQUAL) {
      replaceNode = replaceNegateEQUALQE(n, bv);
    }
  } else if(n.getKind() == kind::LT) {
    replaceNode = replaceLTQE(n, bv);
  } else if(n.getKind() == kind::GT) {
    replaceNode = replaceGTQE(n, bv);
  } else if(n.getKind() == kind::LEQ) {
    replaceNode = replaceLEQQE(n, bv);
  } else if(n.getKind() == kind::GEQ) {
    replaceNode = replaceGEQQE(n, bv);
  } else if(n.getKind() == kind::EQUAL) {
    replaceNode = replaceEQUALQE(n, bv);
  }
  return replaceNode;
}
Node QuantifierEliminate::rewriteRelationOperatorQE(Node n, Node bv,
                                                    QuantifierEliminate q) {
  std::vector<Node> replaceNode;
  Debug("expr-qetest")<<"Node n "<<n<<std::endl;
  Debug("expr-qetest")<<"bound var "<<bv<<std::endl;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      Node c = *i;
      Debug("expr-qetest")<<"Node c "<<c<<std::endl;
      Node temp = replaceRelationOperatorQE(c, bv);
      Debug("expr-qetest")<<"Node temp "<<temp<<std::endl;
      replaceNode.push_back(temp);
    }
    Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),
                                                       replaceNode);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
    return returnNode;
  } else {
    Node returnNode = replaceRelationOperatorQE(n, bv);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
    return returnNode;
  }
}
Node QuantifierEliminate::rewriteForSameCoefficients(Node n, Node bv,
                                                     QuantifierEliminate q) {
  n = parseEquation(n, bv, q);
  n = rewriteRelationOperatorQE(n, bv, q);
  return n;
}

Node QuantifierEliminate::getExpressionWithDivisibility(Node n, Node bv,
                                                        QuantifierEliminate q) {
  Integer lcmVal = lcmValue;
  Debug("expr-qetest")<<"lcmValue in getDivisibility Expression "<<lcmVal<<std::endl;
  if(lcmVal > 1) {
    Node modulus = NodeManager::currentNM()->mkNode(
        kind::INTS_MODULUS, bv, fromIntegerToNodeQE(lcmVal));
    Node modulusExpr = NodeManager::currentNM()->mkNode(kind::EQUAL,
                                                        fromIntegerToNodeQE(0),
                                                        modulus);
    n = NodeManager::currentNM()->mkNode(kind::AND, n, modulusExpr);
    Debug("expr-qetest")<<"Final Node "<<n<<std::endl;
    return n;
  } else {
    return n;
  }
}

Node QuantifierEliminate::doRewriting(Node n, Node bv, QuantifierEliminate q) {
  Node t;
  t = eliminateImpliesQE(n);
  t = convertToNNFQE(t);
  t = rewriteForSameCoefficients(t, bv, q);
  t = getExpressionWithDivisibility(t, bv, q);
  return t;
}

Node QuantifierEliminate::computeLeftProjection(Node n, Node bv,
                                                Integer lcmCalc) {
  Debug("expr-qetest")<<"Given Expression "<<n<<std::endl;
  std::vector<bool> leftProjectionNode;
  std::vector<Node> divisibilityNodes;
  Node returnNode;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      Node child = *i;
      if(child.getKind() == kind::EQUAL) {
        Debug("expr-qetest")<<"divisibility child in lp "<<child<<std::endl;
        divisibilityNodes.push_back(child);
      } else if(child.getKind() == kind::AND || child.getKind() == kind::OR) {
        bool temp1 = true;
        for(Node::iterator j = child.begin(), j_end = child.end(); j != j_end;
        ++j) {
          Node child_inner = *j;
          Debug("expr-qetest")<<"child_inner in lp "<<child_inner<<std::endl;
          Debug("expr-qetest")<<"child_inner[0] in lp "<<child_inner[0]<<std::endl;
          Debug("expr-qetest")<<"child_inner[1] in lp "<<child_inner[1]<<std::endl;
          if(child_inner.getKind() == kind::EQUAL) {
            Debug("expr-qetest")<<"divisibility child_inner in lp "<<child<<std::endl;
            divisibilityNodes.push_back(child_inner);
          } else if(child.getKind() == kind::AND) {
            if(child_inner[0].hasBoundVar()
            && containsSameBoundVar(child_inner[0], bv)) {
              temp1 = temp1 & true;
            } else {
              temp1 = temp1 & false;
            }
          } else {
            if(child_inner[0].hasBoundVar()
            && containsSameBoundVar(child_inner[0], bv)) {
              temp1 = temp1 | true;
            } else {
              temp1 = temp1 | false;
            }
          }
        }
        leftProjectionNode.push_back(temp1);
      } else {
        if(child[0].hasBoundVar() && containsSameBoundVar(child[0], bv)) {

          leftProjectionNode.push_back(true);
        } else {
          leftProjectionNode.push_back(false);
        }
      }

    }
    bool temp = true;
    for(int i = 0; i < (int) leftProjectionNode.size(); i++) {
      if(n.getKind() == kind::AND) {
        temp = temp & leftProjectionNode[i];
      } else {
        temp = temp | leftProjectionNode[i];
      }
    }
    while(!leftProjectionNode.empty()) {
      leftProjectionNode.pop_back();
    }
    returnNode = mkBoolNode(temp);
    if(divisibilityNodes.size() > 1) {
      Node divisibilities = NodeManager::currentNM()->mkNode(kind::AND,
      divisibilityNodes);
      returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
      divisibilities);
    } else if(divisibilityNodes.size() == 1) {
      Node divisibilities = divisibilityNodes.back();
      returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
      divisibilities);
      divisibilityNodes.pop_back();
    } else {
    }
    Debug("expr-qetest")<<"Before rewriting lp "<<returnNode<<std::endl;
    returnNode = Rewriter::rewrite(returnNode);
    Debug("expr-qetest")<<"After rewriting lp "<<returnNode<<std::endl;
    return returnNode;
  } else {
    if(n.getKind() == kind::NOT) {
      if(n[0][0].hasBoundVar() && containsSameBoundVar(n[0][0], bv)) {
        returnNode = mkBoolNode(false);
        if(divisibilityNodes.size() > 1) {
          Node divisibilities = NodeManager::currentNM()->mkNode(
          kind::AND, divisibilityNodes);
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
          returnNode = returnNode.negate();
        } else if(divisibilityNodes.size() == 1) {
          Node divisibilities = divisibilityNodes.back();
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
          returnNode = returnNode.negate();
          divisibilityNodes.pop_back();
        } else {
        }
        Debug("expr-qetest")<<"Before rewriting lp "<<returnNode<<std::endl;
        returnNode = Rewriter::rewrite(returnNode);
        Debug("expr-qetest")<<"After rewriting lp "<<returnNode<<std::endl;
        return returnNode;
      } else {
        returnNode = mkBoolNode(true);
        if(divisibilityNodes.size() > 1) {
          Node divisibilities = NodeManager::currentNM()->mkNode(
          kind::AND, divisibilityNodes);
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
          returnNode = returnNode.negate();
        } else if(divisibilityNodes.size() == 1) {
          Node divisibilities = divisibilityNodes.back();
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
          returnNode = returnNode.negate();
          divisibilityNodes.pop_back();
        } else {
        }
        Debug("expr-qetest")<<"Before rewriting lp "<<returnNode<<std::endl;
        returnNode = Rewriter::rewrite(returnNode);
        Debug("expr-qetest")<<"After rewriting lp "<<returnNode<<std::endl;
        return returnNode;
      }
    } else {
      if(n[0].hasBoundVar() && containsSameBoundVar(n[0], bv)) {
        returnNode = mkBoolNode(true);
        if(divisibilityNodes.size() > 1) {
          Node divisibilities = NodeManager::currentNM()->mkNode(
          kind::AND, divisibilityNodes);
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
        } else if(divisibilityNodes.size() == 1) {
          Node divisibilities = divisibilityNodes.back();
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
          divisibilityNodes.pop_back();
        } else {
        }
        Debug("expr-qetest")<<"Before rewriting lp "<<returnNode<<std::endl;
        returnNode = Rewriter::rewrite(returnNode);
        Debug("expr-qetest")<<"After rewriting lp "<<returnNode<<std::endl;
        return returnNode;
      } else {
        returnNode = mkBoolNode(false);
        if(divisibilityNodes.size() > 1) {
          Node divisibilities = NodeManager::currentNM()->mkNode(
          kind::AND, divisibilityNodes);
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
        } else if(divisibilityNodes.size() == 1) {
          Node divisibilities = divisibilityNodes.back();
          returnNode = NodeManager::currentNM()->mkNode(kind::AND, returnNode,
          divisibilities);
          divisibilityNodes.pop_back();
        } else {
        }
        Debug("expr-qetest")<<"Before rewriting lp "<<returnNode<<std::endl;
        returnNode = Rewriter::rewrite(returnNode);
        Debug("expr-qetest")<<"After rewriting lp "<<returnNode<<std::endl;
        return returnNode;
      }
    }
  }
}
Node QuantifierEliminate::getMinimalExprForRightProjection(Node n, Node bv) {
  Debug("expr-qetest")<<"Given Expression "<<n<<std::endl;
  Debug("expr-qetest")<<"Bound Variable "<<bv<<std::endl;
  std::vector<Node> bExpression;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR)
  {
    for(Node::iterator r_begin = n.begin(), r_end = n.end();
    r_begin != r_end;
    ++r_begin)
    {
      Node childRP = *r_begin;
      if(childRP.getKind() == kind::AND || childRP.getKind() == kind::OR)
      {
        for(Node::iterator inner_begin = childRP.begin(), inner_end = childRP.end();
        inner_begin != inner_end;
        ++inner_begin)
        {
          Node childRP_inner = *inner_begin;
          if(childRP_inner[1].hasBoundVar() && containsSameBoundVar(childRP_inner[1],bv))
          {
            Debug("expr-qetest")<<"b Expression "<<childRP_inner[0]<<std::endl;
            bExpression.push_back(childRP_inner[0]);
          }
        }
      }
      else if(childRP.getKind() == kind::EQUAL) {}
      else
      {
        if(childRP[1].hasBoundVar() && containsSameBoundVar(childRP[1],bv))
        {
          Debug("expr-qetest")<<"b Expression "<<childRP[0]<<std::endl;
          bExpression.push_back(childRP[0]);
        }
      }

    }
  }
  else
  {
    if(n.getKind() == kind::NOT)
    {
      if(n[0][1].hasBoundVar() && containsSameBoundVar(n[0][1],bv))
      {
        Debug("expr-qetest")<<"b Expression "<<n[0][0]<<std::endl;
        bExpression.push_back(n[0][0]);
      }
      else
      {
        Debug("expr-qetest")<<"No bExpression "<<std::endl;
      }
    }
    else
    {
      if(n[1].hasBoundVar() && containsSameBoundVar(n[1],bv))
      {
        Debug("expr-qetest")<<"b Expression "<<n[0]<<std::endl;
        bExpression.push_back(n[0]);
      }
      else
      {
        Debug("expr-qetest")<<"No bExpression "<<std::endl;
      }
    }
  }

  if(bExpression.size()>0)
  {
    Node returnNode = bExpression.back();
    return returnNode;
  }
  else
  {
    Node returnNode = mkBoolNode(false);
    return returnNode;
  }
}

Node QuantifierEliminate::replaceBoundVarRightProjection(Node n, TNode bExpr,
                                                         Node bv) {
  Debug("expr-qetest")<<"Given Expression "<<n<<std::endl;
  Node temp = n;
  for(Node::iterator e_begin = n.begin(), e_end = n.end();
  e_begin != e_end;
  ++e_begin)
  {
    Node childE = *e_begin;
    Debug("expr-qetest")<<"childE in replacement rp "<<childE<<std::endl;
    if(childE.getKind() == kind::AND || childE.getKind() == kind::OR)
    {
      for(Node::iterator eInner_begin = childE.begin(), eInner_end = childE.end();
      eInner_begin != eInner_end;
      ++eInner_begin)
      {
        Node childE_inner = *eInner_begin;
        if(childE_inner[0].hasBoundVar() && containsSameBoundVar(childE_inner[0],bv))
        {
          if(isVarQE(childE_inner[0]))
          {
            TNode toReplace = childE_inner[0];
            temp = temp.substitute(toReplace,bExpr);
          }
          else if(isVarWithCoefficientsQE(childE_inner[0]))
          {
            Node var;
            if(getIntegerFromNode(childE_inner[0][0]) < 0)
            {
              var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
              var = Rewriter::rewrite(var);
            }
            else
            {
              var = bExpr;
            }
            TNode toReplace = childE_inner[0];
            TNode sub = var;
            temp = temp.substitute(toReplace,sub);
          }
          else
          {
            for(Node::iterator inner_begin = childE_inner[0].begin(),inner_end = childE_inner[0].end();
            inner_begin != inner_end;
            ++inner_begin)
            {
              Node innerExpression = *inner_begin;
              if(isVarQE(innerExpression))
              {
                TNode toReplace = innerExpression;
                temp = temp.substitute(toReplace,bExpr);
              }
              else if(isVarWithCoefficientsQE(innerExpression))
              {
                Node var;
                if(getIntegerFromNode(innerExpression[0]) < 0)
                {
                  var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
                  var = Rewriter::rewrite(var);
                }
                else
                {
                  var = bExpr;
                }
                TNode toReplace = innerExpression;
                TNode sub = var;
                temp = temp.substitute(toReplace,sub);
              }
              else
              {}
            }
          }
        }
        if(childE_inner[1].hasBoundVar() && containsSameBoundVar(childE_inner[1],bv))
        {
          if(isVarQE(childE_inner[1]))
          {
            TNode toReplace = childE_inner[1];
            temp = temp.substitute(toReplace,bExpr);
          }
          else if(isVarWithCoefficientsQE(childE_inner[1]))
          {
            Node var;
            if(getIntegerFromNode(childE_inner[1][0]) < 0)
            {
              var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
              var = Rewriter::rewrite(var);
            }
            else
            {
              var = bExpr;
            }
            TNode toReplace = childE_inner[1];
            TNode sub = var;
            temp = temp.substitute(toReplace,sub);
          }
          else
          {
            for(Node::iterator inner_begin = childE_inner[1].begin(),inner_end = childE_inner[1].end();
            inner_begin != inner_end;
            ++inner_begin)
            {
              Node innerExpression = *inner_begin;
              if(isVarQE(innerExpression))
              {
                TNode toReplace = innerExpression;
                temp = temp.substitute(toReplace,bExpr);
              }
              else if(isVarWithCoefficientsQE(innerExpression))
              {
                Node var;
                if(getIntegerFromNode(innerExpression[0]) < 0)
                {
                  var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
                  var = Rewriter::rewrite(var);
                }
                else
                {
                  var = bExpr;
                }
                TNode toReplace = innerExpression;
                TNode sub = var;
                temp = temp.substitute(toReplace,sub);
              }
              else
              {}
            }
          }
        }
      }
    }
    else if(childE.getKind() == kind::EQUAL)
    {
      for(int i=0;i<(int) childE.getNumChildren();i++)
      {
        if(childE[i].getKind() == kind::INTS_MODULUS)
        {
          if(childE[i][0].hasBoundVar() && containsSameBoundVar(childE[i][0],bv))
          {
            TNode toReplace = childE[i][0];
            temp = temp.substitute(toReplace,bExpr);
          }
        }
        else
        {}
      }
    }
    else
    {
      if(childE.hasBoundVar() && containsSameBoundVar(childE,bv))
      {
        TNode toReplace;
        if(isVarQE(childE))
        {
          toReplace = childE;
          temp = temp.substitute(toReplace,bExpr);
        }
        else if(isVarWithCoefficientsQE(childE))
        {
          Node var;
          Debug("expr-qetest")<<"Coefficient of childE "<<getIntegerFromNode(childE[0])<<std::endl;
          if(getIntegerFromNode(childE[0]) < 0)
          {
            var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
            var = Rewriter::rewrite(var);
          }
          else
          {
            var = bExpr;
          }
          Debug("expr-qetest")<<"var to replace "<<var<<std::endl;
          TNode toReplace = childE;
          TNode sub = var;
          temp = temp.substitute(toReplace,sub);
        }
        else
        {
          for(Node::iterator replaceRP = childE.begin(), replaceRPEnd = childE.end();
          replaceRP != replaceRPEnd;
          ++replaceRP)
          {
            Node rp = *replaceRP;
            if(isVarQE(rp) && containsSameBoundVar(rp,bv))
            {
              toReplace = rp;
              temp = temp.substitute(toReplace,bExpr);
              break;
            }
            else if(isVarWithCoefficientsQE(rp) && containsSameBoundVar(rp,bv))
            {
              Node var;
              if(getIntegerFromNode(rp[0]) < 0)
              {
                var = NodeManager::currentNM()->mkNode(kind::MULT,fromIntegerToNodeQE(-1),bExpr);
                var = Rewriter::rewrite(var);
              }
              else
              {
                var = bExpr;
              }
              TNode toReplace = rp;
              TNode sub = var;
              temp = temp.substitute(toReplace,sub);
              break;
            }
            else {}
          }
        }
      }
      else
      {}
    }
  }
  return temp;
}
Node QuantifierEliminate::replaceXForLeftProjection(Node n, Node original,
                                                    Integer rep) {
  TNode tn1 = n;
  Debug("expr-qetest")<<"TNode tn1 "<<tn1<<std::endl;
  Node f = fromIntegerToNodeQE(rep);
  TNode tn2 = f;
  Debug("expr-qetest")<<"TNode tn2 "<<tn2<<std::endl;
  original = original.substitute(tn1, tn2);
  Debug("expr-qetest")<<"Node original after substitution "<<original<<std::endl;
  return original;
}
Node QuantifierEliminate::computeXValueForLeftProjection(Node n,
                                                         Integer lcmCalc) {
  std::vector<Node> leftProjections;
  Node t = n;
  if(t.getKind() == kind::AND || t.getKind() == kind::OR
      || t.getKind() == kind::EQUAL) {
    Integer j = 1;
    while(j <= lcmCalc) {
      if(t.getKind() == kind::AND || t.getKind() == kind::OR) {
        std::vector<Node> innerLefts;
        for(Node::iterator leftP = t.begin(), leftEnd = t.end();
            leftP != leftEnd; ++leftP) {
          Node childLP = *leftP;
          if(childLP.getKind() == kind::EQUAL) {
            if(childLP[0].getKind() == kind::INTS_MODULUS) {
              childLP = replaceXForLeftProjection(childLP[0][0], childLP, j);
              childLP = Rewriter::rewrite(childLP);
              Integer x = getIntegerFromNode(childLP[0][0]);
              if(x.euclidianDivideRemainder(lcmCalc) == 1) {
                innerLefts.push_back(mkBoolNode(false));
              } else {
                innerLefts.push_back(mkBoolNode(true));
              }
            } else {
              childLP = replaceXForLeftProjection(childLP[1][0], childLP, j);
              childLP = Rewriter::rewrite(childLP);
              Integer x = getIntegerFromNode(childLP[1][0]);
              if(x.euclidianDivideRemainder(lcmCalc) == 1) {
                innerLefts.push_back(mkBoolNode(false));
              } else {
                innerLefts.push_back(mkBoolNode(true));
              }
            }
          } else {
          }
        }
        Node lp = NodeManager::currentNM()->mkNode(t.getKind(), innerLefts);
        lp = Rewriter::rewrite(lp);
        leftProjections.push_back(lp);
      } else {
        t = n;
        if(t[0].getKind() == kind::INTS_MODULUS) {
          t = replaceXForLeftProjection(t[0][0], t, j);
          t = Rewriter::rewrite(t);
          Integer y = getIntegerFromNode(t[0][0]);
          if(y.euclidianDivideRemainder(lcmCalc) == 1) {
            leftProjections.push_back(mkBoolNode(false));
          } else {
            leftProjections.push_back(mkBoolNode(true));
          }
        } else {
          t = replaceXForLeftProjection(t[1][0], t, j);
          t = Rewriter::rewrite(t);
          Integer y = getIntegerFromNode(t[1][0]);
          if(y.euclidianDivideRemainder(lcmCalc) == 1) {
            leftProjections.push_back(mkBoolNode(false));
          } else {
            leftProjections.push_back(mkBoolNode(true));
          }
        }
      }
      j = j + 1;
    }
    t = NodeManager::currentNM()->mkNode(kind::OR, leftProjections);
    t = Rewriter::rewrite(t);
    Debug("expr-qetest")<<"Final LeftProjection "<<t<<std::endl;
    return t;
  } else {
    return t;
  }
}

Node QuantifierEliminate::computeRightProjection(Node n, Node bv,
                                                 Integer lcmCalc) {
  Node test = getMinimalExprForRightProjection(n, bv);
  test = Rewriter::rewrite(test);
  Debug("expr-qetest")<<"Minimal Expression "<<test<<std::endl;
  Node result;
  Node rp;
  if(test == mkBoolNode(false)) {
    result = test;
    Debug("expr-qetest")<<"Result After Replacement "<<result<<std::endl;
    return result;
  } else {
    Integer j = 1;
    TNode b;
    Integer lcm = lcmCalc;
    Debug("expr-qetest")<<"lcm in rp "<<lcm<<std::endl;
    Node bExpr;
    std::vector<Node> rightProjections;
    while(j <= lcm) {
      if(isConstQE(test)) {
        Integer y = getIntegerFromNode(test) + j;
        bExpr = fromIntegerToNodeQE(y);
      } else {
        bExpr = NodeManager::currentNM()->mkNode(kind::PLUS, test,
                                                 fromIntegerToNodeQE(j));
      }
      b = bExpr;
      Debug("expr-qetest")<<"before replacement b "<<b<<std::endl;
      rp = replaceBoundVarRightProjection(n, b, bv);
      rightProjections.push_back(rp);
      j = j + 1;
    }
    if(rightProjections.size() > 1) {
      result = NodeManager::currentNM()->mkNode(kind::OR, rightProjections);
      //  result = Rewriter::rewrite(result);
      Debug("expr-qetest")<<"Result After Replacement "<<result<<std::endl;
      return result;
    } else {
      result = rightProjections.back();
      //   result = Rewriter::rewrite(result);
      Debug("expr-qetest")<<"Result After Replacement "<<result<<std::endl;
      return result;
    }
  }

}
Node QuantifierEliminate::normalizeNegative(Node n, Node bv,
                                            QuantifierEliminate q) {
  Node temp = Rewriter::rewrite(n);
  Debug("expr-qetest")<<"After rewrite in normalizeNegative "<<temp<<std::endl;
  temp = rewriteRelationOperatorQE(temp, bv, q);
  Debug("expr-qetest")<<"After relational operator replacement in normalizeNegative "<<temp<<std::endl;
  return temp;
}
Node QuantifierEliminate::performCaseAnalysis(Node n, std::vector<Node> bv,
                                              QuantifierEliminate q) {
  Node var;
  Node left;
  Node right;
  Node temp;
  Node final;
  Node args = n;
  Integer qen = 1;
  Integer numOfQuantElim = q.getNumberOfQuantElim();
  while(bv.size() > 0) {
    Debug("expr-qetest")<<"qen in pca "<<qen<<std::endl;
    if(qen > numOfQuantElim) {
      Debug("expr-qetest")<<"Argument "<<args<<std::endl;
      if(args == mkBoolNode(true) || args == mkBoolNode(false)) {
      } else {
        Node v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, bv);
        Debug("expr-qetest")<<"v "<<v<<std::endl;
        std::vector<Node> children;
        children.push_back(v);
        children.push_back(args);
        args = NodeManager::currentNM()->mkNode(kind::FORALL, children);
      }
      break;
    } else {
      var = bv.back();
      if(var.getNumChildren() > 0) {
        var = var[0];
      }
      if(args == mkBoolNode(true) || args == mkBoolNode(false)) {
        while(!bv.empty()) {
          bv.pop_back();
        }
        break;
      }
      args = args.negate();
      Debug("expr-qetest")<<"args before pca "<<args<<std::endl;
      args = doRewriting(args, var, q);
      Debug("expr-qetest")<<"After rewriting "<<args<<std::endl;
      args = normalizeNegative(args,var,q);
      Debug("expr-qetest")<<"After normalize negative "<<args<<std::endl;
      Integer lcmCalc = lcmValue;
      Debug("expr-qetest")<<"Lcm after rewriting complete "<<lcmCalc<<std::endl;
      temp = computeLeftProjection(args, var, lcmCalc);
      left = computeXValueForLeftProjection(temp, lcmCalc);
      Debug("expr-qetest")<<"left "<<left<<std::endl;
      right = computeRightProjection(args, var, lcmCalc);
      Debug("expr-qetest")<<"right "<<right<<std::endl;
      final = NodeManager::currentNM()->mkNode(kind::OR, left, right);
      args = final.negate();
      args = Rewriter::rewrite(args);
      Debug("expr-qetest")<<"args after pca "<<args<<std::endl;
      bv.pop_back();
      qen = qen + 1;
    }

  }
  Debug("expr-qetest")<<"args "<<args<<std::endl;
  return args;
}

std::vector<Node> QuantifierEliminate::computeMultipleBoundVariables(Node n) {
  std::vector<Node> multipleBoundVars;
  Debug("expr-qetest")<<"n "<<n<<std::endl;
  if(n.getNumChildren() > 1) {
    for(int i = 0; i < (int) n.getNumChildren(); i++) {
      multipleBoundVars.push_back(n[i]);
    }
  } else {
    multipleBoundVars.push_back(n[0]);
  }
  return multipleBoundVars;
}
Node QuantifierEliminate::computeProjections(Node n, QuantifierEliminate q) {
  Node temp1;
  std::vector<Node> temp2;
  Node temp3;
  Node final;
  Node temp;
  Debug("expr-qetest")<<"Initial Node "<<n<<std::endl;
  Debug("expr-qetest")<<"Initial Node kind "<<n.getKind()<<std::endl;
  if(n.getKind() == kind::NOT) {
    negationDone = true;
    negateCount += 1;
    temp = n[0];
    if(temp.getKind() == kind::FORALL) {
      std::vector < Node > bv = computeMultipleBoundVariables(temp[0]);
      boundVar.push_back(bv);
      args.push_back(temp[1]);
      return computeProjections(temp[1], q);
    } else if(temp.getKind() == kind::AND) {
      std::vector<Node> miniscopedNode;
      Node result;
      std::vector<Node> bv_child;
      for(Node::iterator i = temp.begin(), i_end = temp.end(); i != i_end;
          ++i) {
        Node child = *i;
        if(child.getKind() == kind::FORALL) {
          bv_child = computeMultipleBoundVariables(child[0]);
          result = performCaseAnalysis(child[1], bv_child, q);
          miniscopedNode.push_back(result);
        } else {
        }
      }
      if(miniscopedNode.size() > 0) {
        Node newNode = NodeManager::currentNM()->mkNode(kind::AND,
                                                        miniscopedNode);
        Debug("expr-qetest")<<"newNode "<<newNode<<std::endl;
        args.push_back(newNode);
        Integer qen = 1;
        if(q.getNumberOfQuantElim() <= 0) {
          Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
          final = q.getOriginalExpression();
          while(!args.empty()) {
            args.pop_back();
          }
          while(!boundVar.empty())
          {
            boundVar.pop_back();
          }
          Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
          return final;
        }
        else
        {
          bool bvc = false;
          while(!boundVar.empty()) {
            Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
            if(qen > q.getNumberOfQuantElim())
            {
              bvc = true;
              Node a = args.back();
              Debug("expr-qetest")<<"Argument "<<a<<std::endl;
              std::vector<Node> b= boundVar.back();
              if(a == mkBoolNode(true) || a == mkBoolNode(false))
              {
                result = a;
              }
              else
              {
                Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
                Debug("expr-qetest")<<"var "<<var<<std::endl;
                std::vector<Node> children;
                children.push_back(var);
                children.push_back(a);
                result = NodeManager::currentNM()->mkNode(kind::FORALL,children);
              }
              while(!args.empty())
              {
                args.pop_back();
              }
              while(!boundVar.empty())
              {
                boundVar.pop_back();
              }
              break;
            }
            else
            {
              temp1 = args.back();
              Debug("expr-qetest")<<"args "<<temp1<<std::endl;
              temp2 = boundVar.back();
              result = performCaseAnalysis(temp1, temp2,q);
              boundVar.pop_back();
              while(!args.empty()) {
                args.pop_back();
              }
              if(result == mkBoolNode(true) || result == mkBoolNode(false)) {
                while(!boundVar.empty()) {
                  boundVar.pop_back();
                }
                args.push_back(result);
                qen = qen+1;
                break;
              } else {
                args.push_back(result);
                qen = qen+1;

              }
            }
          }
          if(bvc)
          {
            final = result;
          }
          else
          {
            result = args.back();
            final = result;
          }
          final = final.negate();
          while(!args.empty()) {
            args.pop_back();
          }
        }
      } else {
        Integer qen = 1;
        if(q.getNumberOfQuantElim() <= 0) {
          Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
          final = q.getOriginalExpression();
          while(!args.empty()) {
            args.pop_back();
          }
          while(!boundVar.empty())
          {
            boundVar.pop_back();
          }
          Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
          return final;
        }
        else
        {
          bool bvc = false;
          while(!boundVar.empty()) {
            Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
            if(qen > q.getNumberOfQuantElim())
            {
              bvc = true;
              Node a = args.back();
              Debug("expr-qetest")<<"Argument "<<a<<std::endl;
              std::vector<Node> b= boundVar.back();
              if(a == mkBoolNode(true) || a == mkBoolNode(false))
              {
                result = a;
              }
              else
              {
                Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
                Debug("expr-qetest")<<"var "<<var<<std::endl;
                std::vector<Node> children;
                children.push_back(var);
                children.push_back(a);
                result = NodeManager::currentNM()->mkNode(kind::FORALL,children);
              }
              while(!args.empty())
              {
                args.pop_back();
              }
              while(!boundVar.empty())
              {
                boundVar.pop_back();
              }
              break;

            }
            else
            {
              temp1 = args.back();
              Debug("expr-qetest")<<"args "<<temp1<<std::endl;
              temp2 = boundVar.back();
              result = performCaseAnalysis(temp1, temp2,q);
              boundVar.pop_back();
              while(!args.empty()) {
                args.pop_back();
              }
              if(result == mkBoolNode(true) || result == mkBoolNode(false)) {
                while(!boundVar.empty()) {
                  boundVar.pop_back();
                }
                args.push_back(result);
                qen = qen+1;
                break;
              } else {
                args.push_back(result);
                qen = qen+1;
              }
            }
          }
          if(bvc)
          {
            final = result;
          }
          else
          {
            result = args.back();
            final = result;
          }
          final = final.negate();
          while(!args.empty()) {
            args.pop_back();
          }
        }
      }
    } else {
      Debug("expr-qetest")<<"pca called from inside not "<<std::endl;
      Integer qen = 1;
      if(q.getNumberOfQuantElim() <= 0) {
        Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
        final = q.getOriginalExpression();
        while(!args.empty()) {
          args.pop_back();
        }
        while(!boundVar.empty())
        {
          boundVar.pop_back();
        }
        Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
        return final;
      }
      else
      {
        if(boundVar.size() > 0) {
          Node result3;
          bool bvc = false;
          while(!boundVar.empty()) {
            Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
            if(qen > q.getNumberOfQuantElim())
            {
              bvc = true;
              Node a = args.back();
              Debug("expr-qetest")<<"Argument "<<a<<std::endl;
              std::vector<Node> b= boundVar.back();
              if(a == mkBoolNode(true) || a == mkBoolNode(false))
              {
                result3 = a;
              }
              else
              {
                Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
                Debug("expr-qetest")<<"var "<<var<<std::endl;
                std::vector<Node> children;
                children.push_back(var);
                children.push_back(a);
                result3 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
              }
              while(!args.empty())
              {
                args.pop_back();
              }
              while(!boundVar.empty())
              {
                boundVar.pop_back();
              }
              break;

            }
            else
            {
              temp1 = args.back();
              Debug("expr-qetest")<<"args "<<temp1<<std::endl;
              temp2 = boundVar.back();
              result3 = performCaseAnalysis(temp1, temp2,q);
              boundVar.pop_back();
              while(!args.empty()) {
                args.pop_back();
              }
              if(result3 == mkBoolNode(true) || result3 == mkBoolNode(false)) {
                while(!boundVar.empty()) {
                  boundVar.pop_back();
                }
                args.push_back(result3);
                qen = qen +1;
                break;
              } else {
                args.push_back(result3);
                qen = qen +1;
              }
            }
          }
          if(bvc)
          {
            final = result3;
          }
          else
          {
            result3 = args.back();
            final = result3;
          }
          if(negationDone && (negateCount.euclidianDivideRemainder(2) == 0))
          {
            final = final.negate();
          }
          while(!args.empty()) {
            args.pop_back();
          }
        } else {
          final = n;
        }
      }

    }
  } else if(n.getKind() == kind::FORALL) {
    std::vector < Node > bv = computeMultipleBoundVariables(n[0]);
    args.push_back(n[1]);
    boundVar.push_back(bv);
    if(n[1].getKind() == kind::NOT) {
      return computeProjections(n[1][0],q);
    } else {
      return computeProjections(n[1],q);
    }
  } else if(n.getKind() == kind::AND) {
    std::vector<Node> miniscopedNode1;
    Node result1;
    std::vector<Node> bv_child1;
    for(Node::iterator j = n.begin(), j_end = n.end(); j != j_end; ++j) {
      Node child1 = *j;
      if(child1.getKind() == kind::FORALL) {
        bv_child1 = computeMultipleBoundVariables(child1[0]);
        Debug("expr-qetest")<<"Bound var in miniscoping "<<bv_child1.size()<<std::endl;
        result1 = performCaseAnalysis(child1[1], bv_child1,q);
        miniscopedNode1.push_back(result1);
      } else {
      }
    }
    if(miniscopedNode1.size() > 0) {
      Node newNode1 = NodeManager::currentNM()->mkNode(kind::AND,
      miniscopedNode1);
      Debug("expr-qetest")<<"newNode1 "<<newNode1<<std::endl;
      args.push_back(newNode1);
      Integer qen = 1;
      if(q.getNumberOfQuantElim() <= 0) {
        Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
        final = q.getOriginalExpression();
        while(!args.empty()) {
          args.pop_back();
        }
        while(!boundVar.empty())
        {
          boundVar.pop_back();
        }
        Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
        return final;
      }
      else
      {
        bool bvc = false;
        while(!boundVar.empty()) {
          Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
          if(qen > q.getNumberOfQuantElim())
          {
            bvc = false;
            Node a = args.back();
            Debug("expr-qetest")<<"Argument "<<a<<std::endl;
            std::vector<Node> b= boundVar.back();
            if(a == mkBoolNode(true) || a == mkBoolNode(false))
            {
              result1 = a;
            }
            else
            {
              Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
              Debug("expr-qetest")<<"var "<<var<<std::endl;
              std::vector<Node> children;
              children.push_back(var);
              children.push_back(a);
              result1 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
            }
            while(!args.empty())
            {
              args.pop_back();
            }
            while(!boundVar.empty())
            {
              boundVar.pop_back();
            }
            break;
          }
          else
          {
            temp1 = args.back();
            Debug("expr-qetest")<<"args"<<temp1<<std::endl;
            temp2 = boundVar.back();
            result1 = performCaseAnalysis(temp1, temp2,q);
            boundVar.pop_back();
            while(!args.empty()) {
              args.pop_back();
            }
            if(result1 == mkBoolNode(true) || result1 == mkBoolNode(false)) {
              while(!boundVar.empty()) {
                boundVar.pop_back();
              }
              args.push_back(result1);
              qen = qen + 1;
              break;
            } else {
              args.push_back(result1);
              qen = qen + 1;
            }
          }
        }
        if(bvc)
        {
          final = result1;
        }
        else
        {
          result1 = args.back();
          final = result1;
        }
        Debug("expr-qetest")<<"result1 "<<result1<<std::endl;
        while(!args.empty()) {
          args.pop_back();
        }
      }
    } else {
      Debug("expr-qetest")<<"pca called from outside not "<<std::endl;
      Integer qen = 1;
      if(q.getNumberOfQuantElim() <= 0) {
        Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
        final = q.getOriginalExpression();
        while(!args.empty()) {
          args.pop_back();
        }
        while(!boundVar.empty())
        {
          boundVar.pop_back();
        }
        Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
        return final;
      }
      else
      {
        bool bvc = false;
        while(!boundVar.empty()) {
          Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
          if(qen > q.getNumberOfQuantElim())
          {
            bvc = false;
            Node a = args.back();
            Debug("expr-qetest")<<"Argument "<<a<<std::endl;
            std::vector<Node> b= boundVar.back();
            if(a == mkBoolNode(true) || a == mkBoolNode(false))
            {
              result1 = a;
            }
            else
            {
              Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
              Debug("expr-qetest")<<"var "<<var<<std::endl;
              std::vector<Node> children;
              children.push_back(var);
              children.push_back(a);
              result1 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
            }
            while(!args.empty())
            {
              args.pop_back();
            }
            while(!boundVar.empty())
            {
              boundVar.pop_back();
            }
            break;
          }
          else
          {
            temp1 = args.back();
            Debug("expr-qetest")<<"args"<<temp1<<std::endl;
            temp2 = boundVar.back();
            result1 = performCaseAnalysis(temp1, temp2,q);
            boundVar.pop_back();
            while(!args.empty()) {
              args.pop_back();
            }
            if(result1 == mkBoolNode(true) || result1 == mkBoolNode(false)) {
              while(!boundVar.empty()) {
                boundVar.pop_back();
              }
              args.push_back(result1);
              qen = qen + 1;
              break;
            } else {
              args.push_back(result1);
              qen = qen + 1;
            }
          }

        }
        if(bvc)
        {
          final = result1;
        }
        else
        {
          result1 = args.back();
          final = result1;
        }
        while(!args.empty()) {
          args.pop_back();
        }
        Debug("expr-qetest")<<"result1 "<<result1<<std::endl;
      }

    }
  } else {
    Integer qen = 1;
    if(q.getNumberOfQuantElim() <= 0) {
      Debug("expr-qetest")<<"No quantifier to eliminate "<<std::endl;
      final = q.getOriginalExpression();
      while(!args.empty()) {
        args.pop_back();
      }
      while(!boundVar.empty())
      {
        boundVar.pop_back();
      }
      Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
      return final;
    }
    if(boundVar.size() > 0) {
      Node result2;
      bool bvc = false;
      while(!boundVar.empty()) {
        Debug("expr-qetest")<<"qen in cp "<<qen<<std::endl;
        if(qen > q.getNumberOfQuantElim())
        {
          bvc = true;
          Node a = args.back();
          Debug("expr-qetest")<<"Argument "<<a<<std::endl;
          std::vector<Node> b= boundVar.back();
          if(a == mkBoolNode(true) || a == mkBoolNode(false))
          {
            result2 = a;
          }
          else
          {
            Node var = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,b);
            Debug("expr-qetest")<<"var "<<var<<std::endl;
            std::vector<Node> children;
            children.push_back(var);
            children.push_back(a);
            result2 = NodeManager::currentNM()->mkNode(kind::FORALL,children);
          }
          while(!args.empty())
          {
            args.pop_back();
          }
          while(!boundVar.empty())
          {
            boundVar.pop_back();
          }
          break;
        }
        else
        {
          temp1 = args.back();
          Debug("expr-qetest")<<"args "<<temp1<<std::endl;
          temp2 = boundVar.back();
          result2 = performCaseAnalysis(temp1, temp2,q);
          boundVar.pop_back();
          while(!args.empty()) {
            args.pop_back();
          }
          if(result2 == mkBoolNode(true) || result2 == mkBoolNode(false)) {
            while(!boundVar.empty()) {
              boundVar.pop_back();
            }
            args.push_back(result2);
            qen = qen + 1;
            break;
          } else {
            args.push_back(result2);
            qen = qen + 1;
          }
        }

      }
      if(bvc)
      {
        final = result2;
      }
      else
      {
        result2 = args.back();
      }
      Debug("expr-qetest")<<"result2 "<<result2<<std::endl;
      if(negationDone && (negateCount.euclidianDivideRemainder(2) == 1))
      {
        final = result2.negate();
      }
      else
      {
        final = result2;
      }
      while(!args.empty()) {
        args.pop_back();
      }
    } else {
      final = n;
    }
  }
  final = Rewriter::rewrite(final);
  Debug("expr-qetest")<<"return from projection "<<final<<std::endl;
  return final;
}
void QuantifierEliminate::setOriginalExpression(Node n) {
  this->originalExpression = n;
}
Node QuantifierEliminate::getOriginalExpression() {
  return this->originalExpression;
}
void QuantifierEliminate::setNumberOfQuantElim(int x) {
  this->numOfQuantiferToElim = x;
}
Integer QuantifierEliminate::getNumberOfQuantElim() {
  return this->numOfQuantiferToElim;
}
std::vector<ExpressionContainer> QuantifierEliminate::getExpContainer(
    QuantifierEliminate q) {
  return q.expressionContainer;
}
void QuantifierEliminate::setEquivalentExpression(Node n) {
  this->equivalentExpression = n;
}
Node QuantifierEliminate::getEquivalentExpression() {
  return this->equivalentExpression;
}
void QuantifierEliminate::setMessage(std::string s) {
  this->successMessage = s;
}
std::string QuantifierEliminate::getMessage() {
  return this->successMessage;
}

bool QuantifierEliminate::checkType(Node n) {
  Debug("expr-qetest")<<"Given Node "<<n<<std::endl;
  Node check;
  TypeNode t;
  bool b = true;
  if(n.getNumChildren() > 1)
  {
    for(int i=0;i<(int) n.getNumChildren();i++)
    {
      if(n[i].getNumChildren() > 0)
      {
        check = n[i][0];
      }
      else
      {
        check = n[i];
      }
      t = check.getType();
      if(!t.isInteger())
      {
        b = false;
        break;
      }
    }
  }
  else
  {
    t = n[0].getType();
    if(!t.isInteger())
    {
      b = false;
    }
    else
    {
      b = true;
    }
  }
  Debug("expr-qetest")<<"checkType "<<b<<std::endl;
  return b;
}
Node QuantifierEliminate::boundVarTypeChecker(Node n) {
  Debug("expr-qetest")<<"Given Expression  "<<n<<std::endl;
  Node t;
  bool check;
  Node toReturn;
  if(n.getKind() == kind::NOT)
  {
    t = n[0];
    if(t.getKind() == kind::FORALL)
    {
      check = checkType(t[0]);
      if(!check)
      {
        toReturn = mkBoolNode(false);
        return toReturn;
      }
      else
      {
        return boundVarTypeChecker(t[1]);
      }
    }
    else if(t.getKind() == kind::AND)
    {
      for(Node::iterator mBegin = t.begin(),mEnd = t.end();
      mBegin != mEnd;
      ++mBegin)
      {
        Node child = *mBegin;
        if(child.getKind() == kind::FORALL)
        {
          check = checkType(child[0]);
          if(!check)
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
          else
          {
            return boundVarTypeChecker(child[1]);
          }
        }
        else
        {
          return boundVarTypeChecker(child);
        }
      }
    }
    else
    {
      if(t == mkBoolNode(true) || t == mkBoolNode(false))
      {
        return t;
      }
      else
      {
        TypeNode t1;
        for(Node::iterator nBegin = t.begin(),nEnd = t.end();
        nBegin != nEnd;
        ++nBegin)
        {
          Node c = *nBegin;
          Debug("expr-qetest")<<"c in not  "<<c<<std::endl;
          if(isVarQE(c))
          {
            t1 = c.getType();
            if(!t1.isInteger())
            {
              toReturn = mkBoolNode(false);
              return toReturn;
            }
          }
          else if(isVarWithCoefficientsQE(c))
          {
            Debug("expr-qetest")<<"isVarWithCoefficientsQE in not "<<c<<std::endl;
            t1 = c[1].getType();
            Debug("expr-qetest")<<"typenode t1 "<<t1<<std::endl;
            if(!t1.isInteger())
            {
              toReturn = mkBoolNode(false);
              return toReturn;
            }
          }
          else if(isConstQE(c))
          {
            t1 = c.getType();
            Debug("expr-qetest")<<"typenode t1 "<<t1<<std::endl;
            if(!t1.isInteger())
            {
              toReturn = mkBoolNode(false);
              return toReturn;
            }
          }
          else
          {
            Debug("expr-qetest")<<"exp in not "<<c<<std::endl;
            toReturn = boundVarTypeChecker(c);
          }
        }
      }

    }
  }
  else if(n.getKind() == kind::FORALL)
  {
    check = checkType(n[0]);
    if(!check)
    {
      toReturn = mkBoolNode(false);
      return toReturn;
    }
    else
    {
      return boundVarTypeChecker(n[1]);
    }
  }
  else if(n.getKind() == kind::AND)
  {
    for(Node::iterator pBegin = n.begin(),pEnd = n.end();
    pBegin != pEnd;
    ++pBegin)
    {
      Node child1 = *pBegin;

      if(child1.getKind() == kind::FORALL)
      {
        check = checkType(child1[0]);
        if(!check)
        {
          toReturn = mkBoolNode(false);
          return toReturn;
        }
        else
        {
          return boundVarTypeChecker(child1[1]);
        }
      }
      else
      {
        return boundVarTypeChecker(child1);
      }
    }
  }
  else
  {
    if(n == mkBoolNode(true) || n == mkBoolNode(false))
    {
      return n;
    }
    else
    {
      TypeNode t2;
      for(Node::iterator qBegin = n.begin(),qEnd = n.end();
      qBegin != qEnd;
      ++qBegin)
      {
        Node c1 = *qBegin;
        Debug("expr-qetest")<<"c1  "<<c1<<std::endl;
        if(isVarQE(c1))
        {
          t2 = c1.getType();
          if(!t2.isInteger())
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
        }
        else if(isVarWithCoefficientsQE(c1))
        {
          Debug("expr-qetest")<<"isVarWithCoefficientsQE  "<<c1<<std::endl;
          t2 = c1[1].getType();
          Debug("expr-qetest")<<"typenode t2 "<<t2<<std::endl;
          if(!t2.isInteger())
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
        }
        else if(isConstQE(c1))
        {
          t2 = c1.getType();
          Debug("expr-qetest")<<"typenode t2 "<<t2<<std::endl;
          if(!t2.isInteger())
          {
            toReturn = mkBoolNode(false);
            return toReturn;
          }
        }
        else
        {
          Debug("expr-qetest")<<"exp "<<c1<<std::endl;
          toReturn = boundVarTypeChecker(c1);
        }
      }
    }

  }
  Debug("expr-qetest")<<"toReturn "<<toReturn<<std::endl;
  if(toReturn.isNull())
  {
    return mkBoolNode(true);
  }
  else
  {
    return toReturn;
  }

}

Node QuantifierEliminate::prenexChecker(Node n)
{
  Node toReturn;
  if(n.getKind() == kind::NOT)
  {
    Node t = n[0];
    if(t.getKind() == kind::FORALL)
    {
      return prenexChecker(t[1]);
    }
    else if(t.getKind() == kind::AND)
    {
      for(Node::iterator nBegin = n.begin(),nEnd = n.end();
          nBegin != nEnd;
          ++nBegin)
      {
        Node c1 = *nBegin;
        if(c1.getKind() == kind::FORALL)
        {
          return prenexChecker(c1[1]);
        }
        else
        {
          return prenexChecker(c1);
        }
      }
    }
    else
    {
      for(Node::iterator qBegin = t.begin(),qEnd = t.end();
          qBegin != qEnd;
          ++qBegin)
      {
        Node child1 = *qBegin;
        if((child1.getKind() == kind::NOT && child1[0].getKind() == kind::FORALL) || (child1.getKind() == kind::FORALL))
        {
          toReturn = mkBoolNode(false);
          return toReturn;
        }
        else
        {
          toReturn = prenexChecker(child1);
        }
      }
    }
  }
  else if(n.getKind() == kind::FORALL)
  {
    return prenexChecker(n[1]);
  }
  else if(n.getKind() == kind::AND)
  {
    for(Node::iterator mBegin = n.begin(),mEnd = n.end();
        mBegin != mEnd;
        ++mBegin)
    {
      Node c = *mBegin;
      if(c.getKind() == kind::FORALL)
      {
        return prenexChecker(c[1]);
      }
      else
      {
        return prenexChecker(c);
      }
    }
  }
  else
  {
    for(Node::iterator pBegin = n.begin(),pEnd = n.end();
        pBegin != pEnd;
        ++pBegin)
    {
      Node child = *pBegin;
      if((child.getKind() == kind::NOT && child[0].getKind() == kind::FORALL) || (child.getKind() == kind::FORALL))
      {
        toReturn = mkBoolNode(false);
        return toReturn;
      }
      else
      {
        toReturn = prenexChecker(child);
      }
    }
  }
  Debug("expre-qetest")<<"toReturn from prenex checker "<<toReturn<<std::endl;
  return toReturn;
}

QuantifierEliminate QuantifierEliminate::qeEngine(Node n,
                                                  int numOfQuantifiers) {
  Debug("expr-qetest")<<"Before qe  "<<n<<std::endl;
  Debug("expr-qetest")<<"Before qe kind "<<n.getKind()<<std::endl;
  QuantifierEliminate qe;
  qe.setOriginalExpression(n);
  qe.setNumberOfQuantElim(numOfQuantifiers);
  if(numOfQuantifiers <= 0)
  {
    qe.setEquivalentExpression(n);
    std::string s = "error! Number of quantifiers requested to be eliminated is "+ numOfQuantifiers;
    qe.setMessage(s);
    return qe;
  }
  else
  {
    Node temp = n;
    temp = Rewriter::rewrite(temp);
    Node final;
    bool typeCheck,prenexCheck;
    if(boundVarTypeChecker(temp) == mkBoolNode(false))
    {
      typeCheck = false;
    }
    else
    {
      typeCheck = true;
    }
    if(prenexChecker(temp) == mkBoolNode(false))
    {
      prenexCheck = false;
    }
    else
    {
      prenexCheck = true;
    }
    if(typeCheck && prenexCheck)
    {
      Debug("expr-qetest")<<"Type checker has found no problem "<<std::endl;
      Debug("expr-qetest")<<"Prenex checker has found no problem "<<std::endl;
      Debug("expr-qetest")<<"Before qe expression "<<temp<<std::endl;
      final = computeProjections(temp,qe);
      Debug("expr-qetest")<<"After qe "<<final<<std::endl;
      qe.setEquivalentExpression(final);
      qe.setMessage("success");
      return qe;
    }
    else if(!typeCheck)
    {
      Debug("expr-qetest")<<"Type checker failure contains non integer type "<<std::endl;
      qe.setMessage("(Input expression contains non integer type)");
      return qe;
    }
    else
    {
      Debug("expr-qetest")<<"Expression not in prenex form "<<std::endl;
      qe.setMessage("(Input expression not in prenex form)");
      return qe;
    }
  }

}

