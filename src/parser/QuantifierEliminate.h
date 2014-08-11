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
   //static CVC4::TNode convertToPrenex(CVC4::TNode body, std::vector<CVC4::TNode >& args, bool pol);
//   static void setNestedQuantifiers( CVC4::Node n, CVC4::Node q );
//   static void setNestedQuantifiersInner( CVC4::Node n, CVC4::Node q, std::vector< CVC4::Node >& processed );
   //static CVC4::Node convertToNNF(CVC4::Node body);
   //static bool isLiteral(CVC4::Node n);
  // static bool containsQuantifierQe(CVC4::Node n);
  // static CVC4::TNode computePrenexOperation(CVC4::TNode, bool isNested);
  static Node convertToPrenex(Node body, std::vector< Node >& args, bool pol);
public:
  //static CVC4::Node simplifyExpression(const Expr& e);
  //static CVC4::TNode getPrenexExpression(const Expr& e);
  static Node getPrenexExpression(Node n);
};
}
//}
//}
#endif
