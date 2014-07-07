#include<iostream>
#include<vector>
#include "expr/node.h"
#include "expr/expr_template.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "expr/kind.h"
//#include "theory/quantifiers/bounded_integers.h"
using namespace std;
using namespace CVC4;
using namespace CVC4::theory::quantifiers;

// attribute for "contains instantiation constants from"
struct NestedQuantAttributeId {};
typedef expr::Attribute<NestedQuantAttributeId, Node> NestedQuantAttribute;

class QuantifierEliminate {
private:
  CVC4::Expr expression;
  std::vector<Node> d_quants;
  std::vector<Node> d_bound_var;
  std::vector<Node> d_free_var;
  Node computePrenex(Node body,std::vector< Node >& args, bool pol);
  void setNestedQuantifiers( Node n, Node q );
  void setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
  Node computeNNF(Node body);
public:
  QuantifierEliminate(const CVC4::Expr& ex);
  ~QuantifierEliminate();
  CVC4::Expr getExpression();
  void setExpression(const CVC4::Expr& ex);
  /*void parseQuantifiers(const CVC4::Expr& ex);
  * get number of quantifiers
  int getNumQuantifiers();
  * get quantifier
  Node getQuantifier(int i);
  void receiveBoundVariables(const CVC4::Expr& ex);
  void receiveFreeVariables(const CVC4::Expr& ex);*/
  CVC4::Expr getPrenexExpression(const CVC4::Expr& ex);
  void simplifyExpression();


};
