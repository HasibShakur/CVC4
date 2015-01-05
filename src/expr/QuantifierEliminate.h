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
  static std::vector<std::vector<Node> > boundVar;
  static std::vector<Node> args;
  /*static std::vector<Node> variables;
   static std::vector<Node> coefficients;*/
  static std::vector<Container> container;
  static std::vector<ExpressionContainer> expressionContainer;
//  static Node convertToPrenexQE(Node body, std::vector< Node >& args, bool pol);
  static Node convertToNNFQE(Node body);
  static Node doRewriting(Node n, Node bv);
  static Node eliminateImpliesQE(Node body);
//  static Node processRelationOperatorQE(Node n,bool negationEnabled);
//  static Node replaceGEQQE(Node n,bool negationEnabled);
//  static Node replaceGTQE(Node n,bool negationEnabled);
//  static Node replaceLTQE(Node n,bool negationEnabled);
//  static Node replaceLEQQE(Node n,bool negationEnabled);
//  static Node replaceEqualQE(Node n,bool negationEnabled);
//  static Node internalProcessNodeQE(Node n);
//  static Node normalizeAtom(Node n);
  static Node parseEquation(Node n, Node bv);
  static Node computeLeftProjection(Node n, std::vector<Node> bv);
//  static bool evaluateBoolean(Node n);
  static Node computeRightProjection(Node n, std::vector<Node> bv);
//  static Node preProcessingForRightProjection(Node n);
//  static Node preProcessing2ForRightProjection(Node n);
//  static Node evaluateForRightProjection(Node n, Node replacement);
//  static Node computeOperationQE(Node n, bool isNested);
  static Node performCaseAnalysis(Node n, std::vector<Node> bv);
  static std::vector<Node> computeMultipleBoundVariables(Node n);
//  static void setQENestedQuantifiers( Node n, Node q );
//  static void setQENestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
//  static void setAttributesQE( Node in, Node n );
  //static Node replaceForall(Node body);
  static bool isLiteralQE(Node body);
  static bool isConstQE(Node n);
  static bool isVarQE(Node n);
  static bool isVarWithCoefficientsQE(Node n);
  static bool isEquationQE(Node n);
  static bool isRelationalOperatorTypeQE(Kind k);
  static Node rewriteForSameCoefficients(Node n, Node boundVar);
  static void parseCoefficientQE(Node n);
  static Integer calculateLCMofCoeff(std::vector<Integer> coeffs);
  static Integer getIntegerFromNode(Node n);
  static Integer lcmQE(Integer a, Integer b);
  static Node fromIntegerToNodeQE(Integer n);
  static bool containsSameBoundVar(Node n, Node bv);
  static Node rewriteRelationOperatorQE(Node n);
  static Node replaceRelationOperatorQE(Node n);
  static Node replaceGTQE(Node n);
  static Node replaceGEQQE(Node n);
  static Node replaceLEQQE(Node n);
  static Node replaceEQUALQE(Node n);
  static Node replaceLTQE(Node n);
  static Node replaceNegateLTQE(Node n);
  static Node replaceNegateLEQQE(Node n);
  static Node replaceNegateGTQE(Node n);
  static Node replaceNegateGEQQE(Node n);
  static Node replaceNegateEQUALQE(Node n);
public:
//  static Node preRewriteForPrenex(Node n);
//  static Node postRewriteForPrenex(Node n);

  static Node computeProjections(Node n);

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
