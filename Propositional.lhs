Introduction
============

This Haskell module defines a so-called "kernel" for propositional logic. What
is propositional logic? This module is an answer.

The *subject* matter of propositional logic is actually familiar to all of us
programmers. It's all about the Boolean data-type [1], that simple
data-structure defined as

    data Boolean = True | False

But now we want to think about Booleans in a *logical* way. Our concerns are
not about computation, then, but instead about *proof* and *argument*.

What sort of things do we want to prove about Booleans? Well, *true things*, of
course! In fact, we want to determine which Boolean expressions always come out
as true, the so-called "tautologies", and prove that they do so. For example,
we want to be able to prove things such as

   p || not p == True

and prove equivalences such as

   p && (q || r) == (p && q) || (p && r)

which could be rewritten to be of the form ... = True by writing

   (p && (q || r) == (p && q) || (p && q)) == True

A simple way to prove these statements is to just write a program to construct
a truth-table. If the program verifies that every entry in the table comes out
as true, then we can say that the expression is a tautology. But this turns out
to be a hard problem [2], and once we start messing around with really huge
boolean expressions, we might need a much more sophisticated program. And as
our program becomes evermore sophisticated, we might start worrying quite
seriously about whether it contains bugs. And if our code contains bugs and is
being used to verify logic circuits in very expensive microprocessors, then we
might start worrying about losing our jobs!

One way to deal with this problem is to take an axiomatic approach to logic and
implement our axioms in a *kernel*. The kernel is a very, very simple computer
program, whose correctness we can determine just by inspection. The
sophisticated tautology checker calls out to this program via a very simple
interface, and since the interface guarantees correctness, the outputs of our
sophisticated tautology checker are guaranteed to be correct, whether it
contains bugs or not!

Note: this is a *literate Haskell file*. It can be evaluated by any conforming Haskell compiler and interpreter.

The Theorem data-type
=====================

Let's take a quick glance at the interface for our kernel:

> module Propositional (Theorem, Term(..), axiom1, axiom2, axiom3, mp,
>                       inst, theoremTerm) where

Our Theorem data-type is the set of Boolean expressions. But notice that we do
not export its constructors. The type is *abstract*. We engineer things so that
the only way to obtain values in the type is by using the rest of the
interface, and we will show how to carefully define that interface so that the
only values a user can produce are precisely the *tautologies*.

Minimal Connectives
===================

We first need to define our Boolean expressions, and that means deciding on the
primitive Boolean operations.  There's many usual suspects we can choose from
here, and they can be found in the Prelude. There's the function "not" and the
operators (||), (&&), (<=) [3]. But as any electrical engineer will tell you,
most of these are redundant. You can get away with just a simple NAND function
(NOR is the other alternative).

For our kernel, we will try to keep things relatively clean and free of
redundancy and consider just two Boolean functions, from which all others can
be derived. First, we have negation, and then we have implication:

> infixr 8 :=>:

Implication is a funny thing. When we see "p :=>: q" we are supposed to read
"if p then q", but it's easy to trip up with this interpretation. If in doubt,
read it to say "p is false or q is true". That gives you the correct
truth-table:

<<<<<<< HEAD
----------------
p | q | p :=>: q
----------------
T | T |    T
T | F |    F
F | T |    T
F | F |    T
=======
   | p | q | p :=>: q |
   | -----------------|
   | T | T |    T     |
   | T | F |    F     |
   | F | T |    T     |
   | F | F |    T     |
>>>>>>> b713b2353e368bc2c2b1fa087a83afe3494b257c

With negation and implication, we have the following definition for all
possible Boolean expressions, hereafter called "terms".

> data Term a = Var a
>            | Term a :=>: Term a
>            | Not (Term a)
>            deriving (Show,Eq,Ord)

We will call the type "a" here our "alphabet." It's the place from which we
draw our Boolean variables. We're going to use strings later, but we could use
any type we want, so long as it has enough inhabitants to give us all the
variables we need for the problems we expect to solve. Strings are good,
because there is an inexhaustible supply of them, and they are at least
readable to humans. But integers could work just as well, and would work better
as an optimisation.

The data-type definition itself tells us that a term is either a variable drawn
from the alphabet, an implication between two expressions, or the negation of
an expression. Defining a language of expressions using algebraic data-types is
very idiomatic in typed functional programming. In fact, I believe these
algebraic data-types first appeared in the language ML (from which Haskell is
derived) precisely for the purpose we use them here.

Now that we have terms, let's carve out another type that we intend to abstract
in such a way that the only values one can obtain from it are the
tautologies. This amounts to putting a simple wrapper around Term.

> newtype Theorem a = Theorem (Term a) deriving (Eq, Ord)

Every theorem is a term, of course. But not vice-versa! We will not be
exporting the Theorem constructor.

> theoremTerm :: Theorem a -> Term a
> theoremTerm (Theorem t) = t

We'll need some variables for later, so we'll provide some now, drawing from
the alphabet of strings.

> p :: Term String
> q :: Term String
> r :: Term String
> (p,q,r) = (Var "p",Var "q",Var "r")

Axioms
======

And now the juicy part! We need *axioms*. Axioms will be the starting points of
all of our logical proofs. Every single theorem we will obtain outside the
kernel will correspond to a logical proof that a Boolean expression is always a
tautology. The proofs will conclude in Boolean expressions. Their starting
premises will be *axioms*.

Our axioms are themselves tautologies, and therefore belong in our abstract
Theorem type. That is why we export them from our module. We don't want to
export too many axioms, because we want to be really *really* sure that the
axioms are real tautologies, and adding more axioms just gives us more
opportunities to make mistakes. Luckily, it turns out that we will only need
*three* axioms.

Our first axiom looks a bit like the type of the constant function [4]. We read
it as:

    if p then (if q then p)

But it's nicer to read it as

    if p and q then p

In other words, if p is true, then it's still true when we add a hypothesis of
q. That's obviously correct, and you can easily verify it by drawing up a
truth-table.

  ==================================
p | q | q :=> p | p :=> (q :=>: p)
----------------------------------
T | T |    T    |        T
T | F |    T    |        T
F | T |    F    |        T
F | F |    T    |        T

> axiom1 :: Theorem String
> axiom1 = Theorem (p :=>: q :=>: p)

Our next axiom is more complicated. It doesn't look like the type of any
function in Prelude, but we could define such a function. It's usually called
the S-combinator:

> -- sComb :: (p -> q -> r) -> (p -> q) -> p -> r
> -- sComb x y z = (x z) (y z)

Exercise: check the validity of this proposition using a truth-table.

> axiom2 :: Theorem String
> axiom2 = Theorem ((p :=>: q :=>: r) :=>: (p :=>: q) :=>: (p :=>: r))

Our final axiom is a so-called "classical axiom" and governs negation:

> axiom3 :: Theorem String
> axiom3 = Theorem ((Not p :=>: Not q) :=>: q :=>: p)

This axiom doesn't look like the type of any working function in Haskell,
because this is where Boolean logic departs from programming.

Inference
=========

So far, we only have only exported three theorems in our abstract
data-type. These three theorems are the axioms of our logic. But what about all
the myriad other theorems? There are infinitely many of these, so we can't
simply write them all down.

Instead, we'll use a function to get the remaining theorems. This function will
input two theorems and will output new theorems. Such a function is often
called an "inference rule", since it can be understood as a rule of logical
reasoning, where we move from a true statement to other true
statements. Successively applying this rule then corresponds to carrying out
the steps of a logical *proof*.

Our inference rule is called "modus ponens." It is designed to input a theorem
of the form p :=>: q, together with a theorem p, and then to output q. In other
words, it tells us the following:

    1) If p :=>: q is a theorem 2) And p is a theorem 3) Then we can conclude
that q is a theorem.

By inspecting the truth-table for implication, you should be able to convince
yourself that when we input tautologies to this rule, we can only get back
tautologies. So by exporting this rule in our interface, we can be sure that
users of our module will only be able to generate tautologies with it. And
that's just what we want.

We call such a rule which has this property "valid." Sometimes, you'll see
these rules written in the form:

   p :=>: q,   p
   -------------
         q

> mp :: Eq a => Theorem a -> Theorem a -> [Theorem a]
> mp (Theorem (p' :=>: q')) (Theorem p'') = [Theorem q' | p' == p'']
> mp _ _ = []

Note that our function returns a list. That's not a crucial detail. We do this
so that the inference rule can fail when the inputs are not of the correct
form. We could have used the "Maybe" data-type instead, or just thrown an
error.

We will now say that a program which computes a value of type Theorem is a
*proof* or *verification* of a tautology. Because of the way our module has
been defined, the only possible proofs are those which apply our inference rule
mp to our three axioms. In other words, by carefully constructing our module,
we guarantee that users can only produce theorems by writing down correct
proofs! That's the magic of logic kernels. Security through encapsulation via
lovely strong types.

Instantiation
=============

There are still many tautologies which our users cannot obtain. How would they
go about verifying, say

   x :=>: x ?

They can't, obviously! No axiom features the variable "x", and our mp rule does
not introduce the variable either.

Most books on propositional logic get around this problem using something
called "schemas." These books would have us turn our nice elegant axioms into
*functions* which now take arbitrary terms. So axiom1 would become:

> -- axiom1' :: Term a -> Term a -> Theorem a
> -- axiom1' p' q' = Theorem (p' :=>: q' :=>: p')

But notice that this is no longer a single axiom, as we had above, but an
*infinite* collection of axioms, one for each possible term with a given
alphabet. And this leads to an annoying issue.

How do we move between Boolean expressions which basically say the same thing?
Think about the following two tautologies:

   p :=>: p
   q :=>: q

These are *different*, but only trivially so. One is just a relabelling of the
other. And yet, with our module as it is, a user would need to write down two
proofs to get these two theorems, and that's wasted effort. CPU cycles are
cheap these days, but not *that* cheap. So let's cut down on the wastage and
allow users to move between these tautologies via a single inference rule.

> instTerm :: (a -> Term b) -> Term a -> Term b
> instTerm f (Var p')   = f p'
> instTerm f (Not t)    = Not (instTerm f t)
> instTerm f (a :=>: c) = instTerm f a :=>: instTerm f c

> inst :: (a -> Term b) -> Theorem a -> Theorem b
> inst f (Theorem t) = Theorem (instTerm f t)

This rule allows a user to replace variables in a theorem with any other
Boolean expression via a substitution function "f". Exercise: convince yourself
that this rule is always valid!

With our instantiation rule, we can now move from p :=>: p to q :=>: q by
applying

> -- inst (\"p" -> q)

And we can do more. The rule generally allows us to change the alphabet of our
Boolean expressions. We can, for instance, move between a string alphabet and
an integral one with

> -- inst length

And now, because we can instantiate, we don't need our schematic axioms
anymore. A schematic presentation of propositional logic might be common in
fusty maths textbooks, but that's probably because they are written by people
who don't count their clock cycles. See this as an argument for instantiation
rules in logic and an argument against schemas!

Conclusion
==========

And that's that! It turns out (and later, we shall write a program to prove
it), that every single tautology can be obtained using our interface. We just
need three axioms and two inference rules, and then everything we want to prove
about tautologies is verifiable in a secure way.

This is to say that our kernel is "complete." But just as importantly, it is
also "consistent". *Only* tautologies can be obtained using our interface.

Notice how simple our code is, how easy it is to verify its correctness, and
then consider what it allows us to do: with it, we can verify with absolute
confidence every single tautology of propositional logic.

Moreover, we have turned the rough ideas of "proofs", and "axioms" and
"inference rules" into very clear programming terms. Now, if you want to know
what propositional logic is, you just have to read this code. Simple! [5]

Now I should remark that this is all just a toy. I am unlikely to ever need a
logic kernel for propositional logic. I decided to write one because when I
took mathematical logic at university, we skipped over the propositional stuff,
and I wanted to fill in the gaps in my knowledge. And I thought, what better
way to fill in those gaps than by writing a logical kernel?

But there are better reasons to take this approach and better reasons for
writing kernels for logics. When logics more powerful than just boring old
propositions, it quickly turns out to be impossible to write a nice program
which checks what is true or false. The problem is not just hard. It's
undecidable! Thus, we have to go the axiomatic route.

Next up: Utils.lhs

[1] Well, *classical* logic, anyway!
[2] NP-hard, that is.
[3] p <= q for Boolean expressions says that p being true implies that q is
true. This is a very nice thing to observe and it generalises to intuitionistic
logic where there are many more possible truth values than just the usual True
and False. The important point about truth-values is that they can be
[partially] *ordered*, and in Boolean, False < True.
[4] Honk if you like Curry and Howard!
[5] Well, you had to learn Haskell first, didn't you? But then, you had to
learn English too. And if you were learning from a logic textbook, you'd be
expected to know a bit of mathematical symbolism. We often refer to these
requirements as knowing a suitable "metalanguage." What the Haskell code tells
you is that the only metalanguage one needs for logic is the language of
Haskell itself. Standard ML works too. Ever wondered what "ML" stood for? The
sort of code in this file is its raison d'etre.
