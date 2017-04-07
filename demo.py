#!/usr/bin/python3
import sorts
import functions
import solvers

# To change solvers, simply instantiate a different solver
# In this design, sorts and functions are independent of the solver
# but variables, constants, expressions and formulas are solver-specific objects

# Current Concerns
# 1. Every sort and function is a class, regardless of whether it carries any data.
# 2. Unsure how pythonic the interface should be
# 3. Using lots of dictionaries for mapping from solver independent classes
#    (i.e. Sorts and Functions) to solver-specific instantiation functions
# 4. Haven't worked out correct model interface yet
# 5. Connectives/Predicates are indistinguishable from functions of output sort
#    other than Bool -- depends on user to use them correctly
# 6. Order of arguments within params/args passed to function

# Instantiate a solver
s = solvers.CVC4Solver()

# Set logic
s.set_logic('QF_BV')

# Set options
s.set_option('produce-models', 'true')
s.set_option('produce-assertions', 'true')

# Get a bit vector symbol
bvsym1 = sorts.BitVec
# Create a bit vector sort -- still solver-independent at this point
bvsort1 = sorts.construct_sort(bvsym1, 4)

# Demonstrate an alternative way of creating a sort
bvsort2 = sorts.construct_sort('BitVec', 4)

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
bv1 = s.declare_const('bv1', bvsort1)
bv2 = s.declare_const('bv2', bvsort2)

# Now create functions
esym = functions.extract
efun32 = functions.declare_fun(esym, 3, 2)
efun10 = functions.declare_fun(esym, 1, 0)

# Demonstrate function use
subbv1_32 = s.apply_fun(efun32, bv1)
subbv2_32 = s.apply_fun(efun32, bv2)

# The functions are also callable directly
subbv1_10 = efun10(bv1)
subbv2_10 = efun10(bv2)

# Create and apply Equals and Not functions
# Each function is a class that can be instantiated directly
# as well as declared with declare_fun
eqfun = functions.Equals()
notfun = functions.Not()
eq10 = eqfun(subbv1_10, subbv2_10)
eq32 = eqfun(subbv1_32, subbv2_32)
neq32 = notfun(eq32)


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
two = s.theory_const(bvsort1, 2)
bv1eq2 = s.apply_fun(eqfun, bv1, two)

s.Assert(bv1eq2)

# Check sat
s.check_sat()

# Display assertions
print('Solving with the following assertions:')
for a in s.assertions():
    print("\t", a)

# Display whether or not it is satisfiable
print('Result: ', s.sat)

# Print model values
print('bv1 = ', s.get_value(bv1))
print('bv2 = ', s.get_value(bv2))
