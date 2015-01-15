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
std::vector<ExpressionContainer> QuantifierEliminate::expressionContainer;
Integer QuantifierEliminate::lcmValue;

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
  if(n.isVar() && n.getType().isInteger() && !isVarWithCoefficientsQE(n)
      && !isEquationQE(n))
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
void QuantifierEliminate::parseCoefficientQE(Node n) {
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
      } else {
        if(isVarWithCoefficientsQE(child)) {
          if(child[1] == bv) {
            return true;
          } else {
            return false;
          }
        } else {
          if(child == bv) {
            return true;
          } else {
            return false;
          }
        }
      }
    }
    return false;
  }

}
Integer QuantifierEliminate::getLcmResult(Node t, Node bv) {
  std::vector<Integer> boundVarCoeff;
  for(Node::kinded_iterator i = t.begin(t.getKind()), i_end = t.end(
      t.getKind()); i != i_end; ++i) {
    Node child = *i;
    Debug("expr-qetest")<<"child "<<child<<std::endl;
    parseCoefficientQE(child);
  }
  Debug("expr-qetest")<<"Container size "<<container.size()<<std::endl;
  for(int i = 0; i < (int) container.size(); i++) {
    Debug("expr-qetest")<<"Variable "<<container[i].getVariable()<<" Coefficient "<<container[i].getCoefficient()<<std::endl;
  }
  Integer coeff = 1;
  for(int i = 0; i < (int) container.size(); i++) {
    if(container[i].getVariable() == bv) {
      boundVarCoeff.push_back(container[i].getCoefficient());
    }
  }
  Integer lcmResult = calculateLCMofCoeff(boundVarCoeff);
  Debug("expr-qetest")<<"lcm "<<lcmResult<<std::endl;
  lcmValue = lcmResult;
  return lcmResult;
}

Node QuantifierEliminate::parseEquation(Node t, Node bv) {
  Integer coeff = 1;
  Integer lcmResult = getLcmResult(t, bv);
  Debug("expr-qetest")<<"lcm "<<lcmResult<<std::endl;
  Debug("expr-qetest")<<"Container size "<<container.size()<<std::endl;
  for(int i = 0; i < (int) container.size(); i++) {
    if(container[i].getVariable() == bv) {
      coeff = container[i].getCoefficient();
    }
  }
  Debug("expr-qetest")<<"Coeff "<<coeff<<std::endl;
  Integer multiple = lcmResult.euclidianDivideQuotient(coeff.abs());
  Debug("expr-qetest")<<"multiple "<<multiple<<std::endl;
  while(!container.empty()) {
    container.pop_back();
  }
  Debug("expr-qetest")<<"Container size "<<container.size()<<std::endl;
  if(lcmResult == 1 || multiple == 1) {
    Debug("expr-qetest")<<"t "<<t<<std::endl;
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
    Debug("expr-qetest")<<"t "<<t<<std::endl;
    Kind k = n.getKind();
    Debug("expr-qetest")<<"k "<<k<<std::endl;
    Integer multiplier = 1;
    for(Node::iterator i = n.begin(),i_end = n.end();
    i!=i_end;
    ++i)
    {
      Node child = *i;
      Debug("expr-qetest")<<"child "<<child<<std::endl;
      multiplier = 1;
      for(Node::iterator j = child.begin(),j_end = child.end();
      j != j_end;
      ++j )
      {
        Node child1 = *j;
        Debug("expr-qetest")<<"child1 "<<child1<<std::endl;
        if(child1.hasBoundVar() && containsSameBoundVar(child1,bv))
        {
          if(isConstQE(child1)) {}
          else if(isVarQE(child1))
          {
            multiplier = (multiplier*lcmResult).abs();
          }
          else if(isVarWithCoefficientsQE(child1))
          {
            Integer x = getIntegerFromNode(child1[0]).abs();
            multiplier = lcmResult.euclidianDivideQuotient(x);
          }
          else
          {
            for(Node::iterator k = child1.begin(),k_end = child1.end();
            k != k_end;
            ++k)
            {
              Node child2 = *k;
              Debug("expr-qetest")<<"child2 "<<child2<<std::endl;
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
      ExpressionContainer e(child,multiplier);
      Debug("expr-qetest")<<"expression "<<e.getExpression()<<std::endl;
      Debug("expr-qetest")<<"multiplier "<<e.getMultiplier()<<std::endl;
      expressionContainer.push_back(e);
    }
    for(int i= 0;i<(int)expressionContainer.size();i++)
    {
      Debug("expr-qetest")<<"Expression "<<expressionContainer[i].getExpression()<<" multiplier "<<expressionContainer[i].getMultiplier()<<std::endl;
    }
    std::vector<Node> finalExpr;
    for(int i=0;i<(int)expressionContainer.size();i++)
    {
      Node child = expressionContainer[i].getExpression();
      Integer multiple = expressionContainer[i].getMultiplier();
      Kind k1 = child.getKind();
      std::vector<Node> child_expr;
      for(int p=0;p<(int)child.getNumChildren();p++)
      {
        if(isConstQE(child[p]))
        {
          Integer x = getIntegerFromNode(child[p]);
          x = x*multiple;
          Node temp = fromIntegerToNodeQE(x);
          child_expr.push_back(temp);
        }
        else if(isVarQE(child[p]))
        {
          Node var = child[p];
          Node coeff = fromIntegerToNodeQE(multiple);
          Node temp = NodeManager::currentNM()->mkNode(kind::MULT,coeff,var);
          child_expr.push_back(temp);
        }
        else if(isVarWithCoefficientsQE(child[p]))
        {
          Node var = child[p][1];
          Integer b = getIntegerFromNode(child[p][0]);
          b = b*multiple;
          Node coeff = fromIntegerToNodeQE(b);
          Node temp = NodeManager::currentNM()->mkNode(kind::MULT,coeff,var);
          child_expr.push_back(temp);
        }
        else
        {
          std::vector<Node> right;
          Kind k_child = child[p].getKind();
          for(Node::iterator j = child[p].begin(),j_end = child[p].end();
          j!=j_end;
          ++j)
          {
            Node c = *j;
            if(isConstQE(c))
            {
              Integer x = getIntegerFromNode(c);
              x = x*multiple;
              Node c_temp = fromIntegerToNodeQE(x);
              right.push_back(c_temp);

            }
            else if(isVarQE(c))
            {

              Node var = c;
              Node coeff = fromIntegerToNodeQE(multiple);
              Node c_temp = NodeManager::currentNM()->mkNode(kind::MULT,coeff,var);
              right.push_back(c_temp);

            }
            else
            {

              Node var = c[1];
              Integer b = getIntegerFromNode(c[0]);

              b = b*multiple;

              Node coeff = fromIntegerToNodeQE(b);

              Node c_temp = NodeManager::currentNM()->mkNode(kind::MULT,coeff,var);
              right.push_back(c_temp);

            }

          }
          Node temp = NodeManager::currentNM()->mkNode(k_child,right);

          child_expr.push_back(temp);
        }
      }
      Node child_temp = NodeManager::currentNM()->mkNode(k1,child_expr);

      finalExpr.push_back(child_temp);
    }
//    Divisible
//    finalExpr.push_back(divisible);
    Node finalNode = NodeManager::currentNM()->mkNode(k,finalExpr);
    Debug("expr-qetest")<<"FinalNode"<<finalNode<<std::endl;
    return finalNode;
  }

}
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
Node QuantifierEliminate::replaceGTQE(Node n, Node bv) {
  Node left = n[0];
  Node right = n[1];
  Node returnNode;
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
        left = NodeManager::currentNM()->mkNode(kind::PLUS, left, shiftedNodes);
      }
      returnNode = NodeManager::currentNM()->mkNode(kind::LT, right, left);
      return returnNode;
    }
  }
}
Node QuantifierEliminate::replaceGEQQE(Node n, Node bv) {
  Node left = n[0];
  Node right = n[1];
  Node tempLeft;
  Node tempRight;
  Node returnNode;
  if(tempLeft.hasBoundVar() && containsSameBoundVar(tempLeft, bv)) {
    tempLeft = left;
    tempRight = right;
    if(tempLeft.getKind() == kind::PLUS || tempLeft.getKind() == kind::MINUS) {
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
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
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
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
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
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                       fromIntegerToNodeQE(-1));
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
      } else {
        if(isConstQE(tempRight)) {
          Integer x = getIntegerFromNode(tempRight);
          x = x - 1;
          tempRight = fromIntegerToNodeQE(x);
        } else {

          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                       fromIntegerToNodeQE(-1));
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
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftedFromRight,
                                                        fromIntegerToNodeQE(1));
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
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
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        shiftedFromRight,
                                                        fromIntegerToNodeQE(1));
          } else {
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(1));
          }
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                      tempLeft);
      }

    } else {
      if(tempLeft.getKind() == kind::PLUS || tempLeft.getKind() == kind::MINUS) {
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
}
Node QuantifierEliminate::replaceLEQQE(Node n,Node bv) {
  Node left = n[0];
  Node right = n[1];
  Node tempLeft;
    Node tempRight;
    Node returnNode;
    if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
      tempLeft = left;
      tempRight = right;
      if(tempLeft.getKind() == kind::PLUS || tempLeft.getKind() == kind::MINUS) {
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
                  kind::PLUS, tempRight, shiftedFromLeft, fromIntegerToNodeQE(1));
            } else {
              tempRight = NodeManager::currentNM()->mkNode(
                  kind::PLUS, tempRight, fromIntegerToNodeQE(1));
            }
          } else {
            if(!shiftedFromLeft.isNull()) {
              tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
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
                  kind::PLUS, tempRight, shiftedFromLeft, fromIntegerToNodeQE(1));
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
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         fromIntegerToNodeQE(1));
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
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                         fromIntegerToNodeQE(1));
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
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                        fromIntegerToNodeQE(-1));
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
            tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                        fromIntegerToNodeQE(-1));
          }
          returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                        tempRight);
          }
        }
    }
    return returnNode;
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
        Debug("expr-qetest")<<"convertChildL "<<convertChildL<<std::endl;
        shiftedNodes.push_back(convertChildL);
      } else if(isVarWithCoefficientsQE(childL)) {
        Integer neg = getIntegerFromNode(childL[0]) * -1;
        TNode tn1 = childL[0];
        TNode tn2 = fromIntegerToNodeQE(neg);
        childL = childL.substitute(tn1,tn2);
        Debug("expr-qetest")<<"convertChildL "<<childL<<std::endl;
        shiftedNodes.push_back(childL);
      } else {
        Integer neg = getIntegerFromNode(childL) * -1;
        Node convertChildL = fromIntegerToNodeQE(neg);
        Debug("expr-qetest")<<"convertChildL "<<convertChildL<<std::endl;
        shiftedNodes.push_back(convertChildL);
      }
    }
  }
  if(shiftedNodes.size() > 1)
  {
    shift = NodeManager::currentNM()->mkNode(kind::PLUS, shiftedNodes);
    return shift;
  }
  else
  {
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
    if(isConstQE(innerChild)) {}
    else
    {
      if(innerChild.hasBoundVar() && containsSameBoundVar(innerChild, bv)) {
            toReturn = innerChild;
            break;
       }
      else {}
    }

  }
  Debug("expr-qetest")<<"toReturn "<<toReturn<<std::endl;
  return toReturn;
}
Node QuantifierEliminate::replaceEQUALQE(Node n, Node bv) {
  Debug("expr-qetest")<<"Before replacement "<<n<<std::endl;
  Node left = n[0];
  Node right = n[1];
  Node finalLeft;
  Node finalRight;
  Debug("expr-qetest")<<"Bound Variable "<<bv<<std::endl;
  if(left.hasBoundVar() && containsSameBoundVar(left,bv)) {
    Debug("expr-qetest")<<"left side has boundVariable "<<bv<<std::endl;
    if(right.getKind() == kind::PLUS || right.getKind() == kind::MINUS) {
      Node tempLeft = left;
      Node tempRight = right;
      bool flag = false;
      Node shiftFromLeft;
      if(isVarQE(left) || isVarWithCoefficientsQE(left))
      {
        tempLeft = left;
      }
      else
      {
        shiftFromLeft = getShiftedExpression(tempLeft,bv);
        tempLeft = separateBoundVarExpression(tempLeft,bv);
        Debug("expr-qetest")<<"tempLeft "<<tempLeft<<std::endl;
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
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(1),shiftFromLeft);
        }
        else
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(1));
        }

      }
      else
      {
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,tempRight,shiftFromLeft);
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
        }
        else
        {}
      }
      if(!flag1) {
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(-1),shiftFromLeft);
        }
        else
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(-1));
        }

      }
      else
      {
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,tempRight,shiftFromLeft);
        }
      }

      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
      tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
      finalRight);
      Debug("expr-qetest")<<"After replacement returnNode "<<returnNode<<std::endl;
      return returnNode;
    } else {
      Node tempLeft = left;
      Node tempRight = right;
      Node shiftFromLeft;
      if(isVarQE(left) || isVarWithCoefficientsQE(left))
      {
        tempLeft = left;
      }
      else
      {
        shiftFromLeft = getShiftedExpression(tempLeft,bv);
        tempLeft = separateBoundVarExpression(tempLeft,bv);
        Debug("expr-qetest")<<"tempLeft "<<tempLeft<<std::endl;
      }
      if(isConstQE(tempRight)) {
        Integer x = getIntegerFromNode(tempRight);
        x = x + 1;
        TNode tn1 = tempRight;
        TNode tn2 = fromIntegerToNodeQE(x);
        tempRight = tempRight.substitute(tn1, tn2);
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,tempRight,shiftFromLeft);
        }
      } else {
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(1),shiftFromLeft);
        }
        else
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(1));
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
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS,tempRight,shiftFromLeft);
        }
      } else {
        if(!shiftFromLeft.isNull())
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(-1),shiftFromLeft);
        }
        else
        {
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
          fromIntegerToNodeQE(-1));
        }

      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
      tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
      finalRight);
      return returnNode;
    }
  } else {
    Debug("expr-qetest")<<"right side has boundVariable "<<bv<<std::endl;
    if(right.getKind() == kind::PLUS || right.getKind() == kind::MINUS) {
      Node tempLeft = left;
      Node tempRight = right;
      bool flag = false;
      Node shiftFromRight;
      if(isVarQE(right) || isVarWithCoefficientsQE(right))
      {
        tempRight = right;
      }
      else
      {
        shiftFromRight = getShiftedExpression(tempRight,bv);
        tempRight = separateBoundVarExpression(tempRight,bv);
        Debug("expr-qetest")<<"tempRight "<<tempRight<<std::endl;
      }
      for(Node::iterator j = tempLeft.begin(), j_end = tempLeft.end();
      j != j_end;
      ++j)
      {
        Node childJ = *j;
        if(isConstQE(childJ))
        {
          Integer x = getIntegerFromNode(childJ);
          x = x - 1;
          Node change = fromIntegerToNodeQE(x);
          TNode tn1 = childJ;
          TNode tn2 = change;
          tempLeft = tempLeft.substitute(tn1,tn2);
          flag = true;
          break;
        }
        else
        {}
      }
      if(!flag)
      {
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,fromIntegerToNodeQE(-1),shiftFromRight);
        }
        else
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,fromIntegerToNodeQE(-1));
        }
      }
      else
      {
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,shiftFromRight);
        }
      }
      finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
      tempRight);
      Debug("expr-qetest")<<"finalLeft "<<finalLeft<<std::endl;
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
        }
        else
        {}
      }
      if(!flag1) {
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
          fromIntegerToNodeQE(1),shiftFromRight);
        }
        else
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
          fromIntegerToNodeQE(1));
        }
      }
      else
      {
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
          shiftFromRight);
        }
      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
      tempLeft);
      Debug("expr-qetest")<<"finalRight "<<finalRight<<std::endl;
      Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
      finalRight);
      Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
      return returnNode;
    } else {
      Node tempLeft = left;
      Node tempRight = right;
      Node shiftFromRight;
      if(isVarQE(right) || isVarWithCoefficientsQE(right))
      {
        tempRight = right;
      }
      else
      {
        shiftFromRight = getShiftedExpression(tempRight,bv);
        tempRight = separateBoundVarExpression(tempRight,bv);
        Debug("expr-qetest")<<"tempRight "<<tempRight<<std::endl;
      }
      if(isConstQE(tempLeft))
      {
        Integer x = getIntegerFromNode(tempLeft);
        x = x - 1;
        Node change = fromIntegerToNodeQE(x);
        TNode tn1 = tempLeft;
        TNode tn2 = change;
        tempLeft = tempLeft.substitute(tn1, tn2);
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,shiftFromRight);
        }
      }
      else
      {
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,fromIntegerToNodeQE(-1),shiftFromRight);
        }
        else
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,fromIntegerToNodeQE(-1));
        }
      }
      finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
      tempRight);
      Debug("expr-qetest")<<"finalLeft "<<finalLeft<<std::endl;
      tempLeft = left;
      if(isConstQE(tempLeft))
      {
        Integer x = getIntegerFromNode(tempLeft);
        x = x + 1;
        Node change = fromIntegerToNodeQE(x);
        TNode tn1 = tempLeft;
        TNode tn2 = change;
        tempLeft = tempLeft.substitute(tn1, tn2);
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,shiftFromRight);
        }
      }
      else
      {
        if(!shiftFromRight.isNull())
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,fromIntegerToNodeQE(1),shiftFromRight);
        }
        else
        {
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS,tempLeft,fromIntegerToNodeQE(1));
        }
      }
      finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
      tempLeft);
      Node returnNode = NodeManager::currentNM()->mkNode(kind::AND, finalLeft,
      finalRight);
      Debug("expr-qetest")<<"after replacement "<<returnNode<<std::endl;
      return returnNode;
    }

  }

}
Node QuantifierEliminate::replaceLTQE(Node n, Node bv) {
  Node left = n[0];
  Node right = n[1];
  Node shiftExpr;
  Node returnNode;
  if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
    if(isVarQE(left) || isVarWithCoefficientsQE(left)) {
      returnNode = NodeManager::currentNM()->mkNode(kind::LT,left,right);
    } else {
      shiftExpr = getShiftedExpression(left, bv);
      left = separateBoundVarExpression(left, bv);
      if(!shiftExpr.isNull()) {
        right = NodeManager::currentNM()->mkNode(kind::PLUS, right, shiftExpr);
      }
      returnNode = NodeManager::currentNM()->mkNode(kind::LT, left, right);
    }
  } else {
    if(isVarQE(right) || isVarWithCoefficientsQE(right)) {
      returnNode = NodeManager::currentNM()->mkNode(kind::LT,left,right);
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
}
Node QuantifierEliminate::replaceNegateLTQE(Node n, Node bv) {
  n = replaceGEQQE(n[0],bv);
  return n;
}
Node QuantifierEliminate::replaceNegateLEQQE(Node n, Node bv) {
  n = replaceGTQE(n[0], bv);
  return n;
}
Node QuantifierEliminate::replaceNegateGTQE(Node n, Node bv) {
  Node left = n[0][0];
  Node right = n[0][1];
  Node tempLeft;
  Node tempRight;
  Node returnNode;
  if(left.hasBoundVar() && containsSameBoundVar(left, bv)) {
    tempLeft = left;
    tempRight = right;
    if(tempLeft.getKind() == kind::PLUS || tempLeft.getKind() == kind::MINUS) {
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
                kind::PLUS, tempRight, shiftedFromLeft, fromIntegerToNodeQE(1));
          } else {
            tempRight = NodeManager::currentNM()->mkNode(
                kind::PLUS, tempRight, fromIntegerToNodeQE(1));
          }
        } else {
          if(!shiftedFromLeft.isNull()) {
            tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
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
                kind::PLUS, tempRight, shiftedFromLeft, fromIntegerToNodeQE(1));
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
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                       fromIntegerToNodeQE(1));
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
          tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                       fromIntegerToNodeQE(1));
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
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                      fromIntegerToNodeQE(-1));
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
          tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                      fromIntegerToNodeQE(-1));
        }
        returnNode = NodeManager::currentNM()->mkNode(kind::LT, tempLeft,
                                                      tempRight);
      }
    }

  }
  Debug("expr-qetest")<<"ReturnNode "<<returnNode<<std::endl;
  return returnNode;
}
Node QuantifierEliminate::replaceNegateGEQQE(Node n,Node bv) {
  n = replaceLTQE(n[0],bv);
  return n;
}
Node QuantifierEliminate::replaceNegateEQUALQE(Node n, Node bv) {
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
      Debug("expr-qetest")<<"tempLeft "<<tempLeft<<std::endl;
    }
    if(!shiftFromLeft.isNull()) {
      tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                   shiftFromLeft);
    }
    finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft, tempRight);
    tempRight = right;
    if(!shiftFromLeft.isNull()) {
      tempRight = NodeManager::currentNM()->mkNode(kind::PLUS, tempRight,
                                                   shiftFromLeft);
    }
    finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                  tempLeft);
    Node returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                       finalRight);
    Debug("expr-qetest")<<"After replacement returnNode "<<returnNode<<std::endl;
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
      Debug("expr-qetest")<<"tempRight "<<tempRight<<std::endl;
    }
    if(!shiftFromRight.isNull()) {
      tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                  shiftFromRight);
    }
    finalLeft = NodeManager::currentNM()->mkNode(kind::LT, tempLeft, tempRight);
    Debug("expr-qetest")<<"finalLeft "<<finalLeft<<std::endl;
    tempLeft = left;
    if(!shiftFromRight.isNull()) {
      tempLeft = NodeManager::currentNM()->mkNode(kind::PLUS, tempLeft,
                                                  shiftFromRight);
    }
    finalRight = NodeManager::currentNM()->mkNode(kind::LT, tempRight,
                                                  tempLeft);
    Debug("expr-qetest")<<"finalRight "<<finalRight<<std::endl;
    Node returnNode = NodeManager::currentNM()->mkNode(kind::OR, finalLeft,
                                                       finalRight);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
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
      replaceNode = replaceNegateGTQE(n,bv);
    } else if(temp.getKind() == kind::GEQ) {
      replaceNode = replaceNegateGEQQE(n,bv);
    } else if(temp.getKind() == kind::EQUAL) {
      replaceNode = replaceNegateEQUALQE(n, bv);
    }
  } else if(n.getKind() == kind::LT) {
    replaceNode = replaceLTQE(n, bv);
  } else if(n.getKind() == kind::GT) {
    replaceNode = replaceGTQE(n, bv);
  } else if(n.getKind() == kind::LEQ) {
    replaceNode = replaceLEQQE(n,bv);
  } else if(n.getKind() == kind::GEQ) {
    replaceNode = replaceGEQQE(n, bv);
  } else if(n.getKind() == kind::EQUAL) {
    replaceNode = replaceEQUALQE(n, bv);
  }
  return replaceNode;
}
Node QuantifierEliminate::rewriteRelationOperatorQE(Node n, Node bv) {
  std::vector<Node> replaceNode;
  Debug("expr-qetest")<<"Node n"<<n<<std::endl;
  Debug("expr-qetest")<<"bound var "<<bv<<std::endl;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      Node c = *i;
      Node temp = replaceRelationOperatorQE(c, bv[0]);
      replaceNode.push_back(temp);
    }
    Node returnNode = NodeManager::currentNM()->mkNode(n.getKind(),
                                                       replaceNode);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
    return returnNode;
  } else {
    Node returnNode = replaceRelationOperatorQE(n, bv[0]);
    Debug("expr-qetest")<<"returnNode "<<returnNode<<std::endl;
    return returnNode;
  }
}
Node QuantifierEliminate::rewriteForSameCoefficients(Node n, Node bv) {
  if(n.getKind() == kind::NOT) {
    n = parseEquation(n[0], bv);
    n = rewriteRelationOperatorQE(n, bv);
  } else {
    n = parseEquation(n, bv);
    n = rewriteRelationOperatorQE(n, bv);
  }

  return n;
}

Node QuantifierEliminate::doRewriting(Node n, Node bv) {
  Node t;
  t = eliminateImpliesQE(n);
  t = convertToNNFQE(t);
  t = rewriteForSameCoefficients(t, bv);
  return t;
}

Node QuantifierEliminate::computeLeftProjection(Node n, Node bv) {
  std::vector<bool> leftProjectionNode;
  if(n.getKind() == kind::AND || n.getKind() == kind::OR) {
    for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      Node child = *i;
      if(child.getKind() == kind::AND || child.getKind() == kind::OR) {
        bool temp1 = true;
        for(Node::iterator j = child.begin(), j_end = child.end(); j != j_end;
            ++j) {
          Node child_inner = *j;
          if(child.getKind() == kind::AND) {
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
    Node returnNode = mkBoolNode(temp);
    return returnNode;
  } else {
    if(n.getKind() == kind::NOT) {
      if(n[0][0].hasBoundVar() && containsSameBoundVar(n[0][0], bv)) {
        return mkBoolNode(false);
      } else {
        return mkBoolNode(true);
      }
    } else {
      if(n[0].hasBoundVar() && containsSameBoundVar(n[0], bv)) {
        return mkBoolNode(true);
      } else {
        return mkBoolNode(false);
      }
    }
  }
}
Node QuantifierEliminate::computeRightProjection(Node n, Node bv) {

  return n;
}
Node QuantifierEliminate::performCaseAnalysis(Node n, std::vector<Node> bv) {
// Node rewrittenNode = doRewriting(n, bv);
  Node args = n;
  Node var;
  Node left;
  Node right;
  Node final;
  while(bv.size() > 0) {
    var = bv.back();
    args = doRewriting(args, var);
    Debug("expr-qetest")<<"After rewriting "<<args<<std::endl;
    left = computeLeftProjection(args, var);
    Debug("expr-qetest")<<"left "<<args<<std::endl;
    right = computeRightProjection(args, var);
    Debug("expr-qetest")<<"right "<<args<<std::endl;
    final = NodeManager::currentNM()->mkNode(kind::OR, left, right);
    args = final;
    bv.pop_back();
  }
  Debug("expr-qetest")<<"args "<<args<<std::endl;
  return args;
}

std::vector<Node> QuantifierEliminate::computeMultipleBoundVariables(Node n) {
  std::vector<Node> multipleBoundVars;
  Debug("expr-qetest")<<"n[0] "<<n[0]<<std::endl;
  if(n[0].getNumChildren() > 1) {
    for(int i = 0; i < (int) n.getNumChildren(); i++) {
      Debug("expr-qetest")<<"boundVar "<<n[0][i]<<std::endl;
      multipleBoundVars.push_back(n[0][i]);
    }
  }
  else
  {
    Debug("expr-qetest")<<"boundVar "<<n[0]<<std::endl;
    multipleBoundVars.push_back(n[0]);
  }
  return multipleBoundVars;
}
Node QuantifierEliminate::computeProjections(Node n) {
  Node temp1;
  std::vector<Node> temp2;
  Node temp3;
  Node final;
  Node temp;
  Debug("expr-qetest")<<"Initial Node "<<n<<std::endl;
  if(n.getKind() == kind::NOT) {
    temp = n[0];
    if(temp.getKind() == kind::FORALL) {
      std::vector < Node > bv = computeMultipleBoundVariables(temp[0]);
      boundVar.push_back(bv);
      args.push_back(temp[1]);
      return computeProjections(temp[1]);
    } else if(temp.getKind() == kind::AND) {
      std::vector<Node> miniscopedNode;
      Node result;
      std::vector<Node> bv_child;
      for(Node::iterator i = temp.begin(), i_end = temp.end(); i != i_end;
          ++i) {
        Node child = *i;
        if(child.getKind() == kind::FORALL) {
          bv_child = computeMultipleBoundVariables(child);
          result = performCaseAnalysis(child[1], bv_child);
          miniscopedNode.push_back(result);
        } else {
          //case to handle in case of no miniscoping
          // do nothing
        }
      }
      if(miniscopedNode.size() > 0) {
        Node newNode = NodeManager::currentNM()->mkNode(kind::AND,
                                                        miniscopedNode);
        Debug("expr-qetest")<<"newNode "<<newNode<<std::endl;
        args.push_back(newNode.negate());
        while(!boundVar.empty()) {
          temp1 = args.back();
          temp2 = boundVar.back();
          result = performCaseAnalysis(temp1, temp2);
          boundVar.pop_back();
          while(!args.empty()) {
            args.pop_back();
          }
          args.push_back(result);
        }
        Node r = args.back();
        Debug("expr-qetest")<<"r.negate "<<r.negate()<<std::endl;
        final = r.negate();
        args.pop_back();
      } else {
        while(!boundVar.empty()) {
          temp1 = args.back();
          temp2 = boundVar.back();
          result = performCaseAnalysis(temp1, temp2);
          boundVar.pop_back();
          while(!args.empty()) {
            args.pop_back();
          }
          args.push_back(result);
        }
        Node r = args.back();
        Debug("expr-qetest")<<"r.negate "<<r.negate()<<std::endl;
        final = r.negate();
        args.pop_back();
      }
    } else {
      if(boundVar.size() > 0) {
        Node result3;
        while(!boundVar.empty()) {
          temp1 = args.back();
          temp2 = boundVar.back();
          result3 = performCaseAnalysis(temp1, temp2);
          boundVar.pop_back();
          while(!args.empty()) {
            args.pop_back();
          }
          args.push_back(result3);
        }
        Node r = args.back();
        Debug("expr-qetest")<<"r "<<r.negate()<<std::endl;
        final = r.negate();
        args.pop_back();
      } else {
        final = n;
      }
    }
  } else if(n.getKind() == kind::FORALL) {
    std::vector < Node > bv = computeMultipleBoundVariables(n[0]);
    args.push_back(n[1]);
    boundVar.push_back(bv);
    return computeProjections(n[1]);
  } else if(n.getKind() == kind::AND) {
    std::vector<Node> miniscopedNode1;
    Node result1;
    std::vector<Node> bv_child1;
    for(Node::iterator j = n.begin(), j_end = n.end(); j != j_end; ++j) {
      Node child1 = *j;
      if(child1.getKind() == kind::FORALL) {
        bv_child1 = computeMultipleBoundVariables(child1);
        result1 = performCaseAnalysis(child1[1], bv_child1);
        miniscopedNode1.push_back(result1);
      } else {
      }
    }
    if(miniscopedNode1.size() > 0) {
      Node newNode1 = NodeManager::currentNM()->mkNode(kind::AND,
                                                       miniscopedNode1);
      Debug("expr-qetest")<<"newNode1 "<<newNode1<<std::endl;
      args.push_back(newNode1);
      while(!boundVar.empty()) {
        temp1 = args.back();
        temp2 = boundVar.back();
        result1 = performCaseAnalysis(temp1, temp2);
        boundVar.pop_back();
        while(!args.empty()) {
          args.pop_back();
        }
        args.push_back(result1);
      }
      Node r = args.back();
      Debug("expr-qetest")<<"r "<<r<<std::endl;
      final = r;
      args.pop_back();
    } else {
      while(!boundVar.empty()) {
        temp1 = args.back();
        temp2 = boundVar.back();
        result1 = performCaseAnalysis(temp1, temp2);
        boundVar.pop_back();
        while(!args.empty()) {
          args.pop_back();
        }
        args.push_back(result1);
      }
      Node r = args.back();
      Debug("expr-qetest")<<"r "<<r<<std::endl;
      final = r;
      args.pop_back();
    }

  } else {
    if(boundVar.size() > 0) {
      Node result2;
      while(!boundVar.empty()) {
        temp1 = args.back();
        temp2 = boundVar.back();
        result2 = performCaseAnalysis(temp1, temp2);
        boundVar.pop_back();
        while(!args.empty()) {
          args.pop_back();
        }
        args.push_back(result2);
      }
      Node r = args.back();
      Debug("expr-qetest")<<"r "<<r<<std::endl;
      final = r;
      args.pop_back();
    } else {
      final = n;
    }

  }
  Debug("expr-qetest")<<"final "<<final<<std::endl;
  return final;
}
/*  if(n.getKind() == kind::NOT)
 {
 temp = n[0];
 if(temp.getKind() == kind::AND)
 {
 std::vector<Node> miniscopedNode;
 Node result;
 for(Node::iterator i = temp.begin(),i_end = temp.end();
 i!= i_end;
 ++i)
 {
 Node child = *i;
 if(child.getKind() == kind::FORALL)
 {
 std::vector<Node> multipleBoundVars;
 if(child[0].getNumChildren() > 1)
 {
 for(int j= 0 ;j<(int)child[0].getNumChildren();j++)
 {
 multipleBoundVars.push_back(child[0][i][0]);
 }
 }
 else
 {
 multipleBoundVars.push_back(child[0][0][0]);
 }
 // call to case analysis multiple times
 result = performCaseAnalysis(child[1],multipleBoundVars);
 miniscopedNode.push_back(result);
 }
 else
 {}
 }
 if(miniscopedNode.size() > 0)
 {
 final = NodeManager::currentNM()->mkNode(kind::AND,miniscopedNode);
 return final.negate();
 }
 else
 {
 return temp.negate();
 }
 }
 else if(temp.getKind() == kind::FORALL)
 {
 std::vector<Node> multipleBoundVar1;
 if(temp[0].getNumChildren() > 1)
 {
 for(int i = 0;i<(int)temp[0].getNumChildren();i++)
 {
 multipleBoundVar1.push_back(temp[0][i][0]);
 }
 boundVar.push_back(multipleBoundVar1);
 }
 else
 {
 multipleBoundVar1.push_back(temp[0][0]);
 boundVar.push_back(multipleBoundVar1);
 }
 args.push_back(temp[1]);
 return computeProjections(temp[1].negate);
 }
 }
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
 } else {
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
 } else {
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
 if(n.getKind() == kind::NOT) {
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
 }*/

