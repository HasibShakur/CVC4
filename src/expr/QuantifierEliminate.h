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
  static bool isLiteralQE (Node body);
  static bool isRelationalOperatorTypeQE(Kind k);
  static Node doRewriting(Node n,NodeManager* currNM);
  static Node eliminateImpliesQE(Node body);
  static Node processRelationOperatorQE(Node n);
public:
  static Node doPreprocessing(Expr ex);
};
}
#endif
