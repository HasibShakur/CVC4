/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Enumerators for types
 **
 ** Enumerators for types.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__TYPE_ENUMERATOR_H

#include "util/exception.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "util/Assert.h"

namespace CVC4 {
namespace theory {

class NoMoreValuesException : public Exception {
public:
  NoMoreValuesException(TypeNode n) throw() :
    Exception("No more values for type `" + n.toString() + "'") {
  }
};/* class NoMoreValuesException */

class TypeEnumeratorInterface {
  TypeNode d_type;

public:

  TypeEnumeratorInterface(TypeNode type) :
    d_type(type) {
  }

  virtual ~TypeEnumeratorInterface() {}

  virtual Node operator*() throw(NoMoreValuesException) = 0;

  virtual TypeEnumeratorInterface& operator++() throw() = 0;

  virtual TypeEnumeratorInterface* clone() const = 0;

  TypeNode getType() const throw() { return d_type; }

};/* class TypeEnumeratorInterface */

template <class T>
class TypeEnumeratorBase : public TypeEnumeratorInterface {
public:

  TypeEnumeratorBase(TypeNode type) :
    TypeEnumeratorInterface(type) {
  }

  TypeEnumeratorInterface* clone() const { return new T(static_cast<const T&>(*this)); }

};/* class TypeEnumeratorBase */

class TypeEnumerator {
  TypeEnumeratorInterface* d_te;

  static TypeEnumeratorInterface* mkTypeEnumerator(TypeNode type)
    throw(AssertionException);

public:

  TypeEnumerator(TypeNode type) throw() :
    d_te(mkTypeEnumerator(type)) {
  }

  TypeEnumerator(const TypeEnumerator& te) :
    d_te(te.d_te->clone()) {
  }
  TypeEnumerator& operator=(const TypeEnumerator& te) {
    delete d_te;
    d_te = te.d_te->clone();
    return *this;
  }

  ~TypeEnumerator() { delete d_te; }

  Node operator*() throw(NoMoreValuesException) { return **d_te; }
  TypeEnumerator& operator++() throw() { ++*d_te; return *this; }
  TypeEnumerator operator++(int) throw() { TypeEnumerator te = *this; ++*d_te; return te; }

  TypeNode getType() const throw() { return d_te->getType(); }

};/* class TypeEnumerator */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__TYPE_ENUMERATOR_H */