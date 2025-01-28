Given an interactive finitely-presented GSLT T, produce new typed GSLT.

A typed GSLT comes equipped with a **typing span**: typing is a "multirelation", an endospan on a set.  An apex W of such a span enumerates the ways that a term has a type.  Obviously multiple terms can have the same type.  In the presence of modalities, one term can possibly evolve to another in multiple ways.  And terms can have multiple types, both spatial and behavioral.  An element of W is a witness of the typing relation, a derivation of the judgment.




1. Equip with natural transformations type, kind: 1 => T (i.e. from constant functor at terminal object to identity) to adjoin terms type and kind per sort. (Don't need these for sort R, but not clear to me how to exclude.)

2. For each way term A is related to either type_X or kind_X in the context Γ, there is a way x is related to A in Γ

      Γ ⊢ A: s_X
      ——————————————
      Γ, x: A ⊢ x: A

    Probably a natural transformation.  What functors?  Gamma as a product of sorts (top refinements), s_X a refinement of X, A as any refinement of X related to s_X.
    
3. 

      Γ ⊢ A: B    Γ ⊢ C: s
      ————————————————————
      Γ, x: C ⊢ A: B
      
4. 



------------------------------------------

We don't necessarily have to have interaction be binary; if we have

    ⊙: ∏_{i ∈ I} Xᵢ -> P

then we just get |I| different modalities.  But it's a popular choice, so I'll stick with it here and say

    ⊙: X x Y -> P.

If

    Rew: Z -> R

is a rewrite constructor, then we want there to be a unique one-holed context

    K: Z -> X x Y

such that

    ⊙ ⚬ K = s ⚬ Rew.

- Given theory G of a GSLT as a category

  - RHO
  
      ```
      0: 1 -> P
      |: P x P -> P
      !: N x P -> P
      ?: N x (N -> P) -> P
      *: N -> P
      @: P -> N

      comm: N x (N -> P) x P -> R
      s(comm(x, Q, R)) = x?Q | x!R
      t(comm(x, Q, R)) = ev(Q, @R)
      ```

- For each object T, add morphisms `type_T, kind_T: 1 -> T`, i.e. two natural transformations K -> id

	- RHO

		```
		type_P, kind_P: 1 -> P
		type_N, kind_N: 1 -> N
		type_{N -> P}, kind_{N -> P}: 1 -> (N -> P)
		etc.
		```

- For each object T -> T',  a dependent product constructor

	```
	∏:  T x (T -> T') -> T'
	   (A ,  λx.  B) |-> ∏_{x:A}B
	```

	and inference rules

	```
	Γ ⊢ A: s_{T, 1}    Γ, x: A ⊢ B: s_{T', 2}
	—————————————————————————————————————————— prod
	Γ ⊢ ∏_{x:A}B : s_{T -> T', 2}
	``` 

	```
	Γ ⊢ A: s_{T, 1}    Γ, x: A ⊢ B: s_{T', 2}    Γ, x:A ⊢ C: B
	——————————————————————————————————————————————————————————— abs
	Γ ⊢ λx:A.C: ∏_{x:A}B
	``` 


- Dependent-product-like rule for each slot of ô" in LHS rewrites, which induces a modality for terms in that slot.   The premises are judgements assigning a type (T1) to each rewrite constructor parameter 
	- RHO

		First slot: (no x in context for C because x is shared between context and slot)

		```
		comm(x, Q, K): [for(x, K)] | x!(Q) ~> ev(K, @Q)

		Γ ⊢ A: s_{N,1}    Γ ⊢ B: s_{P,2}    Γ, Q: B ⊢ C: s_{P,3}
		—————————————————————————————————————————————————————————
		Γ ⊢ <-|x:A!(Q:B)>C: s_{P,3} 
		```

		Second slot: (no x in context for C because x is shared between context and slot)

		```
		comm(x, Q, K): for(x, K) | [x!(Q)] ~> ev(K, @Q)

		Γ ⊢ A: s_{N,1}    Γ ⊢ B: s_{N->P,2}    Γ, K: B ⊢ C: s_{P,3}
		————————————————————————————————————————————————————————————
		Γ ⊢ <for(x: A, K: B)|->C: s_{P,3}
		```

- Dependent-product-like rules for term constructors taking exponential objects

	- Pi

		```
		

		Γ ⊢ A: s_{N,1}    Γ, x: A ⊢ B: s_{P,2}
		——————————————————————————————————————
		Γ ⊢ Nu(A, λx.B): s_{P,2}
		```

- abs-like rules for term constructors taking exponential objects

	- Pi

		```
		Γ ⊢ A: s_{N,1}    Γ, x: A ⊢ B: C    Γ, x: A ⊢ C: s_{P,2}
		————————————————————————————————————————————————————————
		Γ ⊢ New(λx.B): Nu(A, λx.C)
		```

	    Note that even though λx.λx.T ≡ λx.T (via deBruijn, though we might consider a lambda calculus where they are) and λx.λy.T ≡ λy.λx.T (which couldn't possibly be true in any lambda calculus), we can still do things like

		```
		New(\x.New(\x.B)) = New(\x.B)
		New(\x.New(\y.B)) = New(\y.New(\x.B))
		```

- morphism on processes

	```
	«%: P -> P
	```

	conv-like 	inference rule

	```
	Γ ⊢ s(A): B    Γ ⊢ t(A): B'
	————————————————————————————
	Γ ⊢ s(A): «%B'
	```

- app-like rule for each rewrite target with a use of ev on an exponential object.
	- RHO (TODO: add x to inference rule)

		```
		(TODO: add x to inference rule)
		Γ ⊢ A: <|x:B!(Q:C)>D    Γ ⊢ y: B    Γ ⊢ E: C
		————————————————————————————————————————————— app-like = source of trace, compare cut
		Γ ⊢ A | y!(E): «%ev(ev(λx.λQ.D, y), @E)

		(TODO: If you use x in dependent type of C, what happens when names don't match?)
		Γ ⊢ A: <for(y:C<-x:B){S:D}|>E    Γ ⊢ A: x:B!(F:C)
		—————————————————————————————————————————————————
		Γ ⊢ A | for(y<-x){Q}: «%ev(\y.ev(\S.E, Q), @F)
		```

- cut-like rule for each rewrite target with a use of ev on an exponental object

	```
	for(chan, cont)
	For(Chan, Pi)  Pi type holds lambda Pi(L) and in the consequent we could write ev(L, @E) instead of using sugar
	Γ ⊢ A: <|x:B!(Q:C)>D    Γ ⊢ E: C   Γ ⊢ A: For(y:@C<-B)R
	——————————————————————————————————————————————————— ——— cut-like = target of trace, compare app
	Γ ⊢ ev(\y.R, @E): ev(\Q.D, E)
	```

    From CILL: "Note that terms generated by cut-free proofs are in normal form; in particular, terms generated by the left rules have variables in the head position, so no redexes are created. Redexes only arise as a result of the substitutions performed by applications of the cut rule. Thus all computation is concentrated into the process of cut elimination."



In general, we can have variables in the typing context that refine any of the objects of the theory, but we only need variables that match the contravariant objects in the LHS of a rewrite.  So e.g. rho calculus only needs variables whose types refine the sort of names, while lambda only needs vars whose types refine the sort of lambda terms.
Ambient calculus doesn't have substitution, just new-binding, so it'll have variables whose types refine the sort of names and an abs-like rule for introducing new, but it won't have a corresponding app-like rule.

Blue calculus will have abs-like rules for both abstraction and new, but only an app-like rule for applying a process to a name.  Its variables (if I'm doing this right) will have types that refine the sort of names.

Let me call the conclusion of a judgement an assertion.  We'll have id-like rules for introducing variables on both sides of the turnstile, but the assertion will be refining the same sort.  So in pi calculus,

Γ ⊢ A:s_N:N
————————————————
Γ, x:A:N ⊢ x:A:N

"If in some context Γ we can derive that A is a cube-sort refining the theory-sort of names, then from the added assumption that the variable x is of cube-sort A refining N we can derive that the variable x is of cube-sort A refining N."

In the lambda-cube, types are also terms, so structural types fall out of the non-nullary term constructors.  So in the rho calculus, we have name types of the form @T where T is a process type.  Similarly, in the blue calculus, we have process types Var(T) where T is a name type.
