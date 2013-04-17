/*********************                                                        */
/*! \file theory_strings_type_rules.h
 ** \verbatim
 ** Original author: tiliang
 ** Major contributors: tiliang
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Typing and cardinality rules for the theory of arrays
 **
 ** Typing and cardinality rules for the theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H
#define __CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace strings {

class StringConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    return nodeManager->stringType();
  }
};

class StringConcatTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    unsigned size = 0;
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       if (!t.isString()) {
         throw TypeCheckingExceptionPrivate(n, "expecting string terms");
       }
	}
    return nodeManager->stringType();
  }
};

class RegExpConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    return nodeManager->regexpType();
  }
};

class RegExpConcatTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       if (!t.isRegExp()) {
         throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
       }
	}
    return nodeManager->regexpType();
  }
};

class RegExpOrTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       if (!t.isRegExp()) {
         throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
       }
	}
    return nodeManager->regexpType();
  }
};

class RegExpInterTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       if (!t.isRegExp()) {
         throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
       }
	}
    return nodeManager->regexpType();
  }
};

class RegExpStarTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    TypeNode t = (*it).getType(check);
    if (!t.isRegExp()) {
      throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
    }
	if(++it != it_end) {
      throw TypeCheckingExceptionPrivate(n, "too many regexp");
    }

    return nodeManager->regexpType();
  }
};

class RegExpPlusTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    TypeNode t = (*it).getType(check);
    if (!t.isRegExp()) {
      throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
    }
	if(++it != it_end) {
      throw TypeCheckingExceptionPrivate(n, "too many regexp");
    }

    return nodeManager->regexpType();
  }
};

class RegExpOptTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    TypeNode t = (*it).getType(check);
    if (!t.isRegExp()) {
      throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
    }
	if(++it != it_end) {
      throw TypeCheckingExceptionPrivate(n, "too many regexp");
    }

    return nodeManager->regexpType();
  }
};

class StringToRegExpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    TypeNode t = (*it).getType(check);
    if (!t.isString()) {
      throw TypeCheckingExceptionPrivate(n, "expecting string terms");
    }
	if(++it != it_end) {
      throw TypeCheckingExceptionPrivate(n, "too many terms");
    }

    return nodeManager->regexpType();
  }
};

class StringInRegExpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    TypeNode t = (*it).getType(check);
    if (!t.isString()) {
      throw TypeCheckingExceptionPrivate(n, "expecting string terms");
    }
	++it;
    t = (*it).getType(check);
    if (!t.isRegExp()) {
      throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
    }
	if(++it != it_end) {
      throw TypeCheckingExceptionPrivate(n, "too many terms");
    }

    return nodeManager->booleanType();
  }
};


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H */
