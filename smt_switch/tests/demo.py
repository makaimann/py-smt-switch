#!/usr/bin/python3
from smt_switch import sorts
from smt_switch import functions
from smt_switch import solvers

# To change solvers, simply instantiate a different solver

# Instantiate a solver
s = solvers.CVC4Solver()

# Set logic
s.SetLogic('QF_BV')

# Set options
s.SetOption('produce-models', 'true')
s.SetOption('produce-Assertions', 'true')

# Get a bit vector symbol
bvsym1 = sorts.BitVec
# Create a bit vector sort -- still solver-independent at this point
bvsort1 = sorts.ConstructSort(bvsym1, 4)

# Demonstrate an alternative way of creating a sort
bvsort2 = sorts.ConstructSort('BitVec', 4)

# Demonstrate a third option
# sorts.BitVec is a class that we can instantiate directly
bvsort3 = sorts.BitVec(4)

# Demonstration of behavior
# Returns true because sorts are completely defined by their S-Expression
print('bvsort1 == bvsort2: ',
      bvsort1, ' == ', bvsort2,
      '-->',
      bvsort1 == bvsort2)

# Declare variables -- this returns a z3/cvc4 term depending on the solver used
bv1 = s.DeclareConst('bv1', bvsort1)
bv2 = s.DeclareConst('bv2', bvsort2)

# Now create functions
esym = functions.extract
efun32 = functions.declare_fun(esym, 3, 2)
efun10 = functions.declare_fun(esym, 1, 0)

# Demonstrate function use
subbv1_32 = s.ApplyFun(efun32, bv1)
subbv2_32 = s.ApplyFun(efun32, bv2)

# The functions are also callable directly
subbv1_10 = efun10(bv1)
subbv2_10 = efun10(bv2)

# Create and apply Equals and Not functions
# Each function is a class that can be instantiated directly
# as well as declared with declare_fun
eqfun = functions.Equals()
notfun = functions.Not()
eq10 = eqfun(subbv1_10, subbv2_10)

# you can also use overloaded operators
neq32 = subbv1_32 != subbv2_32

# And the constraints together -- alternatively could
# assert each individually
andfun = functions.declare_fun(functions.And)
both = andfun(eq10, neq32)

# You can check the sort of terms
# Note: For now it just returns a string S-Expression
# Will eventually translate that back to our sort class
# Have to implement SMT-LIB parsing first
# because of parameterized types i.e. (_ BitVec 4)
# Can't enumerate all of them for mapping back to sort class
print('bv1: Sort = ', bv1.sort)
print('both: Sort = ', both.sort)

# You can query the operator and the children -- returns Term
print('Operator:', both.op)
print('Children:', both.children)

# Assert formula
s.Assert(both)

# Create another constraint
two = s.TheoryConst(bvsort1, 2)
bv1eq2 = s.ApplyFun(eqfun, bv1, two)

s.Assert(bv1eq2)

# Check sat
s.CheckSat()

# Display Assertions
print('Solving with the following Assertions:')
for a in s.Assertions():
    print("\t", a)

# Display whether or not it is.Satisfiable
print('Result: ', s.Sat)

# Print model values
print('bv1 = ', s.GetValue(bv1))
print('bv2 = ', s.GetValue(bv2))
