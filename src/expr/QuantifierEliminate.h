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
  static Node convertToNNFQE(Node body,NodeManager* currNM);
  static Node doRewriting(Node n,NodeManager* currNM);
  static Node eliminateImpliesQE(Node body);
  static Node processRelationOperatorQE(Node n,bool negationEnabled);
  static Node replaceGEQQE(Node n,bool negationEnabled);
//  static Node replaceGTQE(Node n,bool negationEnabled);
  static Node replaceLTQE(Node n,bool negationEnabled);
//  static Node replaceLEQQE(Node n,bool negationEnabled);
//  static Node replaceEqualQE(Node n,bool negationEnabled);
  static Node internalProcessNodeQE(Node n);
public:
  static Node doPreprocessing(Expr ex);
  static bool isLiteralQE (Node body);
  static bool isRelationalOperatorTypeQE(Kind k);
};
}
#endif
