#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"



namespace CVC4{
//class SmtEngine;
//namespace qe{
class CVC4_PUBLIC QuantifierEliminate {
private:
   //CVC4::Node normalizeBody(CVC4::Node body);
   static CVC4::Node convertToPrenex(CVC4::Node body, std::vector<CVC4::Node >& args, bool pol);
   static void setNestedQuantifiers( CVC4::Node n, CVC4::Node q );
   static void setNestedQuantifiersInner( CVC4::Node n, CVC4::Node q, std::vector< CVC4::Node >& processed );
   //static CVC4::Node convertToNNF(CVC4::Node body);
   //static bool isLiteral(CVC4::Node n);
   static bool containsQuantifierQe(CVC4::Node n);
public:
  //static CVC4::Node simplifyExpression(const Expr& e);
  static CVC4::Node getPrenexExpression(const Expr& e);
};
}
//}
//}
#endif
