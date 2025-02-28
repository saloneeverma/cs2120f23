/-!
Note: These notes are not yet complete. They
current extend the material presented at the
end of lecture 3, August 29, 2023. This section
will be extended as we go forward.

# Generalization and Specialization

Consider the following three functions. 
-/

def id_nat : Nat → Nat
| n => n

def id_string : String → String
| n => n

def id_bool : Bool → Bool
| n => n

/-!
Each one returns the value of its single 
argument. We call such function *identity
functions*. We thus have identity functions
for arguments of types Nat, String, and Bool,
respectively. Here are example applications.
-/

#eval id_nat 7
#eval id_string "Hello"
#eval id_bool true

#eval id_nat 5
#eval id_string "Hi"
#eval id_bool false

/-!
Beyond having different names, these
functions vary only in the types of
their argument and return values. 

We wouldn't want to have to write one
such function for each of hundreds of
types. We can avoid such repetition by
"factoring out" the varying part of the
definition into a parameter (argument). 
-/

/-!
## Parametric Polymorphism

A key idea throughout computer science
and mathematics is that we can generalize
families of definitions by turning aspects 
that vary into parameters. Then by giving
specific values for parameters, we recover
the specialied versions.

In the cases above, the main aspect that 
varies is the *type* of objects that are 
being handled: Bools, Strings, Nats. The 
code for each implementation is identical
so we should really only have to write it
once, in a general way, using the idea of
generalization. 

To do this, we introduce a new argument: one
that can take on *any* type value whatsoever. 
We could call this argument, *T : Type*, but in 
Lean it's conventional to use lower-case Greek
letters to name type-valued arguments, so we'll
call it *α : Type.* Here's the code we want.
-/

def id_poly : (α : Type) → α → α 
| α, v => v

/-
The key idea in play here is that we bind a name, 
α, to the value of the (first) type parameter, and,
having done that, we then express the rest of the 
function type in terms of α. In more detail, here
are the elements of the whole function definition:

- def is the keyword for giving a definition
- id_poly is the name of the function being defined
- (α : Type) binds the name α to the first (type) argument 
- in this context, the rest of the function type is α → α 
- the | gives the pattern matching rule for this function
- the names α and v bind to the first and the second arguments
- => separates the pattern on the left from the return value on the right
- v, bound to the second argument, is the return value of this function
- the name α is unused after the => and so can be replaced by _ 
-/

-- And we can see that it works!
#eval id_poly String "Hello!"
#eval id_poly Nat 7
#eval id_poly Bool true

#eval id_poly String "Gi"


/-!
## Specialization by (partial) application 

For example, if α is Nat, the rest of the function 
is of type Nat → Nat. In the single pattern matching
rule, we bind v to the first unnamed argument, a Nat, 
and the function then returns the value of v. If α is 
String, v will be bound to a String given as a second
argument, and the function will return that value.  
-/

#check (id_poly)          -- generalized definition
#check (id_poly Nat)      -- specialization to Nat
#check (id_poly Bool)     -- specialization to Bool
#check (id_poly String)   -- specialization to String

/-!
We can specialize the generalized function to specific types
by applying it only to a first type argument. 
-/

def id_nat' := id_poly Nat        -- same as id_nat above
def id_string' := id_poly String  -- same as id_string above
def id_bool' := id_poly Bool      -- same as id_bool above

#eval id_nat' 7
#eval id_string' "Hello"
#eval id_bool' true

/-!
What we see here is an example of what, in programming, 
is called *parametric polymorphism*. We have one function
definition that can take arguments of many different types. 
Here the *types* of the second argument and return value 
are given by the *value* (a type!) of the first argument. 

Lean detects type errors in such expressions. For example,
if we pass Bool as the first argument but 7 as the second, 
Lean  will report an error. Let's try. 
-/

--#check id_poly Bool 7   -- Lean can't convert 7 into a Bool

/-!
## Implicit Arguments

You might have noticed that in principle Lean can always infer
the *type value* of the first argument to the id_poly function
from the *data value* passed as the second argument. For example,
if the second argument is "Hello!", the first argument just *has
to be* String. If the second argument is 7, the first has to be 
Nat. If the second is true, the first has to be Bool.

In these cases, you can ask Lean to silently fill in argument
values when it knows what they must be, so that you don't have 
to write them explicitly. To tell Lean you want it to infer the
value of the first *type* argument to id_poly, you specify it as 
an argument when defining the function not using (α : Type) but 
using curly braces instead: {α : Type}. Let's define the function 
again (with the name id_poly') to see this idea in action.
-/

def id_poly' : {α : Type} → α → α   -- α is an implicit argument 
| _, v => v

/-!
Now we can write applications of id_poly' without giving the
first (*type*) argument explicitly. It's there, but we don't
have to write it. Instead, Lean infers what it's value must
be from context: specifically from the type of the value we
pass as the second argument. The resulting code is beautifully
simple and evidently polymorphic. It also eliminates possible
type mismatches between the first and second arguments, as the
type in question is inferred automatically from the value to 
be returned. 
-/

#eval id_poly' 7          -- α = Nat, inferred!
#eval id_poly' "Hello!"   -- α = String, inferred!
#eval id_poly' true       -- α = Bool, inferred!

/-!
## Extended Example: A polymorphic apply2 function

We'll now work up to defining a polymorphic function,
apply2, that takes as its arguments a function, f, 
and a value, a, and that returns the result of applying
f to a twice: that it, it returns the value of f (f a).

### A Natty Example

We'll define apply2 as a function that takes a 
function, f, and an argument, a, to that function 
as its arguments, and that then returns the result 
of applying the function f to the argument a twice.
That is, apply will return the value of f (f a).

As an example, if f is the function, Nat.succ, that 
returns one more than a given natural number a, the 
result of "applying f twice to 0" is *succ (succ 0)*,
where inner expression reduces to 1 and the successor
of that is 2. That's the result.

Let's write this apply2 function where the function
and argument values are Natty. We define *apply2_nat*
that takes (1) a function, *f : Nat → Nat*, and (2) a 
second argument, *a : Nat*, and that returns a result 
of applying f twice to a: namely *f (f a)*. 
-/

-- This apply2 version is specialized for Natty values                         f         a
def apply2_nat : (Nat → Nat) → Nat → Nat
| f, a => f (f a)

/-!
Let's apply this function to some arguments to see 
what we get. First we need some specific function,
f, taking and returning a Nat. The Nat.succ function
will work. This is the *successor* function, which
returns 1 more than any natural number given as an
argument. 
-/

#check (Nat.succ)           -- Nat → Nat
#eval Nat.succ 0            -- 1
#eval apply2_nat Nat.succ 0 -- expect 2

/-!
Yay, it seems to work. It gets more interesting when we
see that we can use *any* function of type Nat → Nat as
a first argument to this function.  Here are a few little
puzzles for you to complete by defining simple functions.

First, define a function, *double : Nat → Nat* that 
returns twice the argument to which it's applied. So for
example, *double 4* should reduce to *8*.
-/

def double : Nat → Nat
| n => 2 * n

#eval apply2_nat double 4     -- expect 16 (2 * (2 * 4))
#eval apply2_nat double 10    -- expect 40 (2 * (2 * 10))

/-!
Second, define a function, *square : Nat → Nat*, that 
reduces to its argument value squared. Then check to see
that apply2_nat works when you give square as the first
argument? For example squaring 5 gives 25, and squaring 25 
gives 625, so apply2_nat square 5 should reduce to 625. 
Write both the function definition and test cases for a 
few inputs, including 5. Give your answer here:

#A. define the *square* function here:
-/

-- here:
def square: Nat → Nat
| n => n*n

/-!
Write test cases for apply2_nat square for several values,
including 5, and use them to develop confidence that your
function definition appears to be working more generally.
-/

-- here:

#eval apply2_nat square 5

#eval apply2_nat square 3

#eval apply2_nat square 1



/-! 
### A Stringy Example

Now if you think about it, we should be able to
write an apply2 function that does the analogous
thing but with Stringy things. Given a function, f, 
from String to String, and an argument, a : String,
we can always compute *f (f a )*. 

Your new puzzle is to write apply2_string; then give
examples of applying this function to two different 
function arguments, and for each of those, to several
string argument values.

You can make up your own String → String functions.
For example, a function, exclaim : String → String,
applied to a string, s, could (append s "!"). There
is a notation for this: *s ++ "!"*. Go ahead and 
complete its definition here.
-/

-- here, fill in the missing expression

def exclaim : String → String 
| s => s++"!"    -- with s bound to first argument value

#check (exclaim "Hello")
#eval exclaim "Hello"
#eval exclaim (exclaim "Hello")

/-!
Now you can use this function, exclaimm as a first
argument to apply2_string. The result is a function
that is waiting for an argument, s, and that then
returns returns the result of applying the "baked 
in") function, f, to s, to compute (f s), and then 
applies f to that value, for the second time. The
result is the value of *f (f s))*.  

Show that you can write the programs analogous
to the corresponding ones for Natty things but
now for Stringy things, while writing demo and
test cases. Key idea: A test case defines some
value to be computed *and* an expected result.
The passing or failure of a test case reflects
the consistency of expected and compute value.

## Generalizing the Type of Objects Handled

At this point it should be clear, by analogy
with earlier material, that we can generalize
over the specific Nat and String types in the
previous examples to a general type: call it α!
Replace the _ here with the *rest of the type*
of the apply2 function, given that we alrady
have a specific type in hand, such as String
or Nat, to which we've bound α. You can now
use α to specify the rest of the type of the
function.  
-/

def apply2 : (α : Type) → (α → α) → α → α  
| _, f, a => f (f a)


#eval apply2 Nat Nat.succ 0   -- expect 2
#eval apply2 Nat double 1     -- expect 4
#eval apply2 Nat square 2     -- expect 16
#eval apply2 String exclaim "Hello" 

/-!
## Type Inference

As a final exercise in good notation, redefine
apply2 (calling it apply2') so that the first
argument, the type value, is implicit: where
Lean infers its value from the types of the 
remaining arguments. When you get it right, the
following test cases should work.
-/

-- Now you can and should write the code here:

def apply2' : {α : Type} → (α → α) → α → α  
| _, f, a => f (f a)

-- same tests again
#eval apply2' Nat.succ 0   -- expect 2
#eval apply2' double 1     -- expect 4
#eval apply2' square 2     -- expect 16
#eval apply2' exclaim "Hello" -- Hello!!