# Adding to smt-switch

## Structure

smt-switch consists of 5 modules:
* api - This contains the smt class which is the only object users should interact with
* solvers - This module contains multiple python files, one for each solver. These make use of the solvers' python API to implement the various functions and returns a raw term, i.e. a CVC4Solver's ApplyFun method returns a raw CVC4 Expr. This is then wrapped by the smt object from the api module.
* sorts - This module contains classes for each smt sort. Some are parameterized, e.g. a bitvector has a width. Sorts are accesible through the smt object.
* terms - There is a term for each supported solver. These terms wrap the raw solver variables. After a CheckSat call, you can  query the solver with smt.GetValue which sets value of the term. These terms know how to retrieve data from the solver-specific objects.
* functions - This module contains an OrderedDict of function names to fdata. fdata defines the number of indices, min arity, max arity, and (optionally) custom function behavior. From the function names, function enums are automatically generated and operators (a class to hold functions) are generated for each function and added to the smt object when instantiated.

## Adding a solver

To add a new solver, create a new class that inherits SolverBase. You will need to implement all of the abstract methods. Users never interact directly with a solver. Instead, they issue all commands through an smt object. The smt object calls the solver's method of the same name and wraps the result. In short, the solver is only responsible for producing an object of it's own type and does not need to know anything about smt-switch terms. 

You will need to map from function enums to implementations. The smt-switch standard is to use a dictionary from function enums to python functions, using lambdas when necessary. See an existing solver for examples. You will also need to map smt-switch sorts to the solver's implementation. Note, this mapping is from the sort class, e.g. sorts.BitVec -->  ExprManager().mkBitVectorType for CVC4. Thus when passed a sort in declare const, you check the sorts class, sort.\_\_class\_\_, for the translation. This is important for parameterized types like bitvectors which cannot be enumerated. All options in smt-switch are taken directly from SMT-LIB. If the solver you're adding does not use the SMT-LIB names, you will need to have a dict for translation.

## Adding a function

To add a function, simply add the function name and a corresponding fdata (see below) instance to the func_symbols OrderedDict. Everything else will be automatically generated, and the function operator will be accessible from the smt object.

fdata is a named tuple containing information about the function
fdata(num_indices, min_arity, max_arity, custom_behavior)
* num_indices is the number of indices for an indexed function. For example, extract in the bitvector theory has num_indices=2
* min_arity is the minimum arity of the function
* max_arity is the maximum arity of the function
* custom_behavior is a function that is called if config.strict==False when the number of function arguments is not in [min_arity, max_arity]

Example: 'Extract': fdata(2, 1, 1, None) 

You will also need to add the function's implementation to each solver. This is a mapping from func_enums.(function name) to the implementation.

Finally, you will need to provide a function for computing the function's output sort. This dictionary is in the terms module. Assume the function will be passed all the arguments to the function, and it will need to return the sort. Some functions always return the same sort, others are parameterized. 

Examples

* Equals: lambda x: sorts.Bool()  -- return sort is always bool
* Ite: lambda x, y, z: z          -- return sort is the same as it's arguments

Note, for now term's childrens are all kept track of at the smt-switch level. In a future version, term's sort and children will be queried from the underlying smt solver. This is important because of internal simplification, but has not been implemented yet.

## Adding a sort

Simply add a new class to the sorts.py file with all of the attributes your sort needs. Then in each solver that supports your new sort, add a dictionary entry from the sort class to the solver's implementation.

## Adding an smt command

Add a method to the smt class in api.py. From that method, call the solver method of the same name. Add the method to the SolverBase class in solvers/solverbase.py, and to each of the other solvers.
