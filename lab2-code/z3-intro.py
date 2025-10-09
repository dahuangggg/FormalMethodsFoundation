from z3 import *
from pro_print import *

# Z3 is an SMT solver. In this lecture, we'll discuss
# the basis usage of Z3 through some working example, the
# primary goal is to introduce how to use Z3 to solve
# the satisfiability problems we've discussed in the past
# several lectures.
# We must emphasize that Z3 is just one of the many such SMT
# solvers, and by introducing Z3, we hope you will have a
# general understanding of what such solvers look like, and
# what they can do.

########################################
# Basic propositional logic

# In Z3, we can declare two propositions just as booleans, this
# is rather natural, for propositions can have values true or false.
# To declare two propositions P and Q:
P = Bool('P')
Q = Bool('Q')
# or, we can use a more compact shorthand:
P, Q = Bools('P Q')


# We can build propositions by writing Lisp-style abstract
# syntax trees, for example, the disjunction:
# P \/ Q
# can be encoded as the following AST:
F = Or(P, Q)
# Output is : Or(P, Q)
print(F)

# Note that the connective '\/' is called 'Or' in Z3, we'll see
# several other in the next.

# We have designed the function 'pretty_print(expr)' for you, 
# As long as we input the expression defined by z3, we can output 
# propositions that are suitable for us to read.
# Here‘s an example:

P, Q = Bools('P Q')
F = Or(P, Q)

# Output is : P \/ Q
pretty_print(F)

################################################################
##                           Part A                           ##
################################################################

# Helper function to prove tautologies
def prove_tautology(expr, name):
    print(f"{name}:")
    pretty_print(expr)
    prove(expr)
    print()

# exercises 1 : P -> (Q -> P)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q = Bools('P Q')
exercise1 = Implies(P, Implies(Q, P))
prove_tautology(exercise1, "Exercise 1") 


# exercise 2 : (P -> Q) -> ((Q -> R) -> (P -> R))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q, R = Bools('P Q R')
exercise2 = Implies(Implies(P, Q), Implies(Implies(Q, R), Implies(P, R)))
prove_tautology(exercise2, "Exercise 2") 

# exercise 3 : (P /\ (Q /\ R)) -> ((P /\ Q) /\ R)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q, R = Bools('P Q R')
exercise3 = Implies(And(P, And(Q, R)), And(And(P, Q), R))
prove_tautology(exercise3, "Exercise 3") 

# exercise 4 : (P \/ (Q \/ R)) -> ((P \/ Q) \/ R)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q, R = Bools('P Q R')
exercise4 = Implies(Or(P, Or(Q, R)), Or(Or(P, Q), R))
prove_tautology(exercise4, "Exercise 4") 

# exercise 5 : ((P -> R) /\ (Q -> R)) -> ((P /\ Q) -> R)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q, R = Bools('P Q R')
exercise5 = Implies(And(Implies(P, R), Implies(Q, R)), Implies(And(P, Q), R))
prove_tautology(exercise5, "Exercise 5") 
    
# exercise 6 : ((P /\ Q) -> R) <-> (P -> (Q -> R))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q, R = Bools('P Q R')
left = Implies(And(P, Q), R)
right = Implies(P, Implies(Q, R))
exercise6 = And(Implies(left, right), Implies(right, left))
prove_tautology(exercise6, "Exercise 6") 
    
# exercise 7 : (P -> Q) -> (¬Q -> ¬P)
# Please use z3 to define the proposition
# Note that you need to define the proposition, and prove it.
P, Q = Bools('P Q')
exercise7 = Implies(Implies(P, Q), Implies(Not(Q), Not(P)))
prove_tautology(exercise7, "Exercise 7") 


################################################################
##                           Part B                           ##
################################################################

# Before writing the src first, we need to understand the
# quantifier. ∀ x.P (x) means that for any x, P (x) holds, 
# so both x and P should be a sort types. IntSort() and BoolSort() 
# are given in Z3
# IntSort(): Return the integer sort in the given context.
# BoolSort(): Return the Boolean Z3 sort.
isort = IntSort()
bsort = BoolSort()
  
# Declare a Int variable x
x = Int('x')

# Declare a function P with input of isort type and output 
# of bsort type
P = Function('P', isort, bsort)

# It means ∃x.P(x)
F = Exists(x, P(x))
print(F)
pretty_print(F)

# Now you can complete the following exercise based on the example above

# exercise 8 : ∀x.(¬P(x) /\ Q(x)) -> ∀x.(P(x) -> Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)

left8 = ForAll(x, And(Not(P(x)), Q(x)))
right8 = ForAll(x, Implies(P(x), Q(x)))
exercise8 = Implies(left8, right8)
prove_tautology(exercise8, "Exercise 8") 

# exercise 9 : ∀x.(P(x) /\ Q(x)) <-> (∀x.P(x) /\ ∀x.Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)

left9 = ForAll(x, And(P(x), Q(x)))
right9 = And(ForAll(x, P(x)), ForAll(x, Q(x)))
exercise9 = And(Implies(left9, right9), Implies(right9, left9))
prove_tautology(exercise9, "Exercise 9") 

# exercise 10 : ∃x.(¬P(x) \/ Q(x)) -> ∃x.(¬(P(x) /\ ¬Q(x)))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)

left10 = Exists(x, Or(Not(P(x)), Q(x)))
right10 = Exists(x, Not(And(P(x), Not(Q(x)))))
exercise10 = Implies(left10, right10)
prove_tautology(exercise10, "Exercise 10") 

# exercise 11 : ∃x.(P(x) \/ Q(x)) <-> (∃x.P(x) \/ ∃x.Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)

left11 = Exists(x, Or(P(x), Q(x)))
right11 = Or(Exists(x, P(x)), Exists(x, Q(x)))
exercise11 = And(Implies(left11, right11), Implies(right11, left11))
prove_tautology(exercise11, "Exercise 11") 

# exercise 12 : ∀x.(P(x) -> ¬Q(x)) -> ¬(∃x.(P(x) /\ Q(x)))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)

left12 = ForAll(x, Implies(P(x), Not(Q(x))))
right12 = Not(Exists(x, And(P(x), Q(x))))
exercise12 = Implies(left12, right12)
prove_tautology(exercise12, "Exercise 12") 

# exercise 13 : ∃x.(P(x) /\ Q(x)) /\ ∀x.(P(x) -> R(x)) -> ∃x.(R(x) /\ Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
P = Function('P', isort, bsort)
Q = Function('Q', isort, bsort)
R = Function('R', isort, bsort)

left13 = And(Exists(x, And(P(x), Q(x))), ForAll(x, Implies(P(x), R(x))))
right13 = Exists(x, And(R(x), Q(x)))
exercise13 = Implies(left13, right13)
prove_tautology(exercise13, "Exercise 13") 

# exercise 14 : ∃x.∃y.P(x, y) -> ∃y.∃x.P(x, y)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
y = Int('y')
P = Function('P', isort, isort, bsort)

left14 = Exists(x, Exists(y, P(x, y)))
right14 = Exists(y, Exists(x, P(x, y)))
exercise14 = Implies(left14, right14)
prove_tautology(exercise14, "Exercise 14") 

# exercise 15 : P(b) /\ (∀x.∀y.(P(x) /\ P(y) -> x = y)) -> (∀x.(P(x) <-> x = b))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
isort = IntSort()
bsort = BoolSort()
x = Int('x')
y = Int('y')
b = Int('b')
P = Function('P', isort, bsort)

left15 = And(P(b), ForAll([x, y], Implies(And(P(x), P(y)), x == y)))
right15 = ForAll(x, And(Implies(P(x), x == b), Implies(x == b, P(x))))
exercise15 = Implies(left15, right15)
prove_tautology(exercise15, "Exercise 15") 


################################################################
##                           Part C                           ##
################################################################

# Challenge: 
# We provide the following two rules :
#     ----------------(odd_1)
#           odd 1
#
#           odd n
#     ----------------(odd_ss)
#         odd n + 2
#
# Please prove that integers 9, 25, and 99 are odd numbers.

isort = IntSort()
bsort = BoolSort()

odd = Function('odd', isort, bsort)

n = Int('n')

rule1 = odd(1)
rule2 = ForAll(n, Implies(odd(n), odd(n + 2)))

print("Part C Challenge:")
print("Rule 1 (odd_1):")
pretty_print(rule1)
print("Rule 2 (odd_ss):")
pretty_print(rule2)
# print("Rule 2 raw:", rule2)
print()

# Create solver and add the rules
s = Solver()
s.add(rule1)
s.add(rule2)

# Prove that 9 is odd
print("Proving 9 is odd:")
s.push()
s.add(Not(odd(9)))
result = s.check()
if result == unsat:
    print("9 is odd (proven)")
else:
    print("Cannot prove 9 is odd")
s.pop()

# Prove that 25 is odd
print("Proving 25 is odd:")
s.push()
s.add(Not(odd(25)))
result = s.check()
if result == unsat:
    print("25 is odd (proven)")
else:
    print("Cannot prove 25 is odd")
s.pop()

# If 25 is proven odd, add it as a fact to help prove larger odd numbers
if result == unsat:
    s.add(odd(25))

# Prove that 99 is odd
print("Proving 99 is odd:")
s.push()
s.add(Not(odd(99)))
result = s.check()
if result == unsat:
    print("99 is odd (proven)")
else:
    print("Cannot prove 99 is odd")
s.pop()

print()
print("All exercises completed!") 



