#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"

namespace CVC4{
class CVC4_PUBLIC QuantifierEliminate {
private:
  static Node convertToPrenexQE(Node body, std::vector< Node >& args, bool pol);
  static Node convertToNNFQE(Node body);
  static Node doRewriting(Node n, Node boundVar);
  static Node eliminateImpliesQE(Node body);
//  static Node processRelationOperatorQE(Node n,bool negationEnabled);
//  static Node replaceGEQQE(Node n,bool negationEnabled);
//  static Node replaceGTQE(Node n,bool negationEnabled);
//  static Node replaceLTQE(Node n,bool negationEnabled);
//  static Node replaceLEQQE(Node n,bool negationEnabled);
//  static Node replaceEqualQE(Node n,bool negationEnabled);
//  static Node internalProcessNodeQE(Node n);
//  static Node normalizeAtom(Node n);
  static bool computeLeftProjection(Node n, Node boundVar);
//  static bool evaluateBoolean(Node n);
  static Node computeRightProjection(Node n, Node boundVar);
//  static Node preProcessingForRightProjection(Node n);
//  static Node preProcessing2ForRightProjection(Node n);
//  static Node evaluateForRightProjection(Node n, Node replacement);
  static Node replaceForall(Node n);
  static Node performCaseAnalysis(Node n,Node boundVar);
public:
  static Node doPreprocessing(Expr ex);
  static bool isLiteralQE (Node body);
  static bool isRelationalOperatorTypeQE(Kind k);
  static Node computeProjections(Node n,std::vector<Node> boundVar,std::vector<Node> args);
};
}
#endif
