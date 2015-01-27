#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "theory/arith/normal_form.h"
namespace CVC4 {
class Container;
class ExpressionContainer;
class CVC4_PUBLIC QuantifierEliminate {
private:
  //static variables

  static std::vector<std::vector<Node> > boundVar;
  static std::vector<Node> args;

  //non static variables
  Integer lcmValue;
  Integer numOfQuantiferToElim;
  Node originalExpression;
  std::vector<Container> container;
  std::vector<ExpressionContainer> expressionContainer;

  //static methods

  static Node convertToNNFQE(Node body);
  static std::vector<Node> computeMultipleBoundVariables(Node n);
  static bool isLiteralQE(Node body);
  static bool isConstQE(Node n);
  static bool isVarQE(Node n);
  static bool isVarWithCoefficientsQE(Node n);
  static bool isEquationQE(Node n);
  static bool isRelationalOperatorTypeQE(Kind k);
  static Integer getIntegerFromNode(Node n);
  static Node fromIntegerToNodeQE(Integer n);
  static bool containsSameBoundVar(Node n, Node bv);
  static Integer lcmQE(Integer a, Integer b);
  static Node getShiftedExpression(Node n, Node bv);
  static Node separateBoundVarExpression(Node n, Node bv);
  static Node performCaseAnalysis(Node n, std::vector<Node> bv, QuantifierEliminate q);
  Node computeProjections(Node n, QuantifierEliminate q);

  //non static methods

  Node doRewriting(Node n, Node bv, QuantifierEliminate q);
  static Node eliminateImpliesQE(Node body);
  Node parseEquation(Node n, Node bv, QuantifierEliminate q);
  Node computeLeftProjection(Node n, Node bv, QuantifierEliminate q);
  Node computeRightProjection(Node n, Node bv, QuantifierEliminate q);

  Node rewriteForSameCoefficients(Node n, Node boundVar, QuantifierEliminate q);
  void parseCoefficientQE(Node n, QuantifierEliminate q);
  Integer calculateLCMofCoeff(std::vector<Integer> coeffs);
  Node rewriteRelationOperatorQE(Node n, Node bv, QuantifierEliminate q);
  Node replaceRelationOperatorQE(Node n, Node bv);
  Node replaceGTQE(Node n, Node bv);
  Node replaceGEQQE(Node n, Node bv);
  Node replaceLEQQE(Node n, Node bv);
  Node replaceEQUALQE(Node n, Node bv);
  Node replaceLTQE(Node n, Node bv);
  Node replaceNegateLTQE(Node n, Node bv);
  Node replaceNegateLEQQE(Node n, Node bv);
  Node replaceNegateGTQE(Node n, Node bv);
  Node replaceNegateGEQQE(Node n, Node bv);
  Node replaceNegateEQUALQE(Node n, Node bv);
  Integer getLcmResult(Node t, Node bv, QuantifierEliminate q);

  Node getExpressionWithDivisibility(Node n, Node bv, QuantifierEliminate q);
  Node getMinimalExprForRightProjection(Node n, Node bv);
  Node replaceBoundVarRightProjection(Node n, TNode bExpr, Node bv);
  Node computeXValueForLeftProjection(Node n, QuantifierEliminate q);
  Node replaceXForLeftProjection(Node n, Node original, Integer rep);

  void setOriginalExpression(Node n);
  Node getOriginalExpression();
  void setNumberOfQuantElim(int x);
  Integer getNumberOfQuantElim();
  void setLcmValue(Integer x);
  Integer getLcmValue();
  void setContainer(std::vector<Container> c);
  std::vector<Container> getContainer();
  void setExpContainer(std::vector<ExpressionContainer> ec);
  std::vector<ExpressionContainer> getExpContainer();

  //  static Node convertToPrenexQE(Node body, std::vector< Node >& args, bool pol);
  //  static bool evaluateBoolean(Node n);
//  static Node preProcessingForRightProjection(Node n);
//  static Node preProcessing2ForRightProjection(Node n);
//  static Node evaluateForRightProjection(Node n, Node replacement);
//  static Node computeOperationQE(Node n, bool isNested);
//  static void setQENestedQuantifiers( Node n, Node q );
//  static void setQENestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
//  static void setAttributesQE( Node in, Node n );
  //static Node replaceForall(Node body);
public:
//  static Node preRewriteForPrenex(Node n);
//  static Node postRewriteForPrenex(Node n);
  static Node qeEngine(Node n, int numOfQuantifiers);

};

class Container {
private:
  Node variable;
  Integer coefficient;
public:
  Container(Node v, Integer c) {
    variable = v;
    coefficient = c;
  }
  Node getVariable() {
    return variable;
  }
  Integer getCoefficient() {
    return coefficient;
  }
  void setCoefficient(Integer c) {
    coefficient = c;
  }
};
class ExpressionContainer {
private:
  Node expression;
  Integer multiplier;
public:
  ExpressionContainer(Node e, Integer i) {
    expression = e;
    multiplier = i;
  }
  Node getExpression() {
    return expression;
  }
  Integer getMultiplier() {
    return multiplier;
  }
  void setExpression(Node e) {
    expression = e;
  }
  void setMultiplier(Integer i) {
    multiplier = i;
  }

};
}
#endif
