#include<iostream>
#include "expr/node.h"
#include "expr/expr_template.h"
#include "parser/input.h"
#include "parser/parser.h"
using namespace std;
using namespace CVC4;

class QuantifierEliminate{
 private:
	CVC4::Expr expression;
 public:
	QuantifierEliminate(const CVC4::Expr& ex);
	~QuantifierEliminate();
	CVC4::Expr getExpression();
};
