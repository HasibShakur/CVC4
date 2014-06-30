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

namespace kind {
  namespace metakind {
    struct NodeValueConstPrinter;
  }/* CVC4::kind::metakind namespace */
}/* CVC4::kind namespace */
class QuantifierEliminate{
 private:
	CVC4::Expr expression;
	std::vector< Node > d_quants;
 public:
	QuantifierEliminate(const CVC4::Expr& ex);
	~QuantifierEliminate();
	CVC4::Expr getExpression();
	void parseQuantifiers(const CVC4::Expr& ex);
	/** get number of quantifiers */
	int getNumQuantifiers();
	/** get quantifier */
	Node getQuantifier( int i );

};
