proplcf
=======

I gave a talk at Edlambda a few years ago about how much I love Edinburgh LCF. I wrote a demo in Haskell as a side-effect, which is probably a bad idea for many reasons (you allow infinitely large propositions, for starters).

When I did maths as an undergraduate, we skipped over the metatheory of propositional logic, in order to fast-track Goedel's Theorems. So I never got to prove things such as the Deduction Theorem for Hilbert's axioms of propositional logic, and I didn't have any good practice doing the proofs needed to get to completeness.

So I decided to do a Hilbert style propositional calculus in Haskell, and then do the proofs there. I had a lot of fun, and I think it's a nice way to explore how one builds up the metatheory of propositional logic, so that one can avoid all the pain that comes from using Hilbert style proofs. 

If you want to start at the beginning, just work with the file Propositional.hs. This gives you three axiom schemas for propositional logic, a way to instantiate those schemes, and modus ponens. That's all you need to formally derive any proposition. The code is very simple, because it's a *kernel*: it's supposed to be so trivial that you can verify the correctness by hand. The three axioms are obviously true classically, and modus ponens is obviously a valid inference rule.

But you can't do simple things like making assumptions. So if you want a headstart, play with Bootstrap.hs, and check out the proofs in that. They're not too painful to read and write.

If you want to think in terms of logical equivalences and substitution, use Conversions.hs. This is not complete, but there's enough to start doing some basic equational reasoning.

If you want to think in terms of sequents, use Sequents.hs. This gives you a much much nicer, composable way to do proofs than Bootstrap.hs

I haven't got very far with Tactics.hs.