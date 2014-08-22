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
//  static Node convertToNNFQE(Node body);
 // static bool isLiteralQE (Node body);
 /* static bool isClauseQE( Node n );
  static bool isCubeQE( Node n );
  static void addNodeToOrBuilderQE( Node n, NodeBuilder<>& t );
  static Node mkForAllQE( std::vector< Node >& args, Node body, Node ipl );
  static void computeArgsQE( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n );
  static void computeArgVecQE( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static bool hasArgQE( std::vector< Node >& args, Node n );
  static void setNestedQuantifiersQE( Node n, Node q );
  static void setNestedQuantifiers2QE( Node n, Node q, std::vector< Node >& processed );
  static Node computeClauseQE( Node n );
  static Node computeCNFQE( Node n, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred );*/

public:
  static Node doPreprocessing(Expr ex);
};
}
#endif
