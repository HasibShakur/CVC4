#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"

namespace CVC4{
class CVC4_PUBLIC QuantifierEliminate {
private:
   //CVC4::Node normalizeBody(CVC4::Node body);
   static Node convertToNNF(Node body);
   static bool isLiteral(Node n);
  static Node convertToPrenex(Node body, std::vector< Node >& args, bool pol);
public:
  static Node simplifyExpression(Node n);
  static Node getPrenexExpression(Node n);
};
}
#endif
