Given an interactive finitely-presented GSLT T, produce new typed GSLT.

- E.g. RHO calculus

    ```
    shape
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.
      N
    
    fn syms
      0: 1 -> P
      |: P x P -> P
      !: N x P -> P
      ?: N x (N -> P) -> P
      *: N -> P
      @: P -> N

    eqns
      // V = P from above
      comm. mon. eqns
      @*n = n

    rewrites
      comm: N x (N -> P) x P -> R
      comm: x?Q | x!R ~> ev(Q, @R)
    
      par1: R x P -> R
      par1: s(r) | p ~> t(r) | p
    
      par2: R x R -> R
      par2: s(r1) | s(r2) ~> t(r1) | t(r2)
    
      run: P -> P
      run: *@P ~> P
    ```

- E.g. λ-calculus

    ```
    shape
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.

    fn syms
      App: P x P -> P
      Lam: (P -> P) -> P
    
    eqns
      // V = P from above
    
    rewrites
      beta: (P -> P) x P -> R
      beta: App(Lam(K), Q) ~> ev(K, Q)
      
      head: R x P -> R
      head: App(s(E), Q) ~> App(t(E), Q)
    ```
      
We'll consider the free theory on empty sets.  Since it's free, we get an algebra for building up terms and a coalgebra for taking them apart.  That lets us do destructuring assignment in the premises of an inference rule.

We'll add term constructors and a typing endospan : on terms in a typing context.

Judgments are of the form A: B where A and B are both terms (which may include free variables) of the same shape.  We write s^T to indicate that there are up to two rules, depending on where you are in the hypercube: one for type^T, one for kind^T (see Axiom below for those terms).  We can read "A: B" as "a way that A relates to B", since a span allows A to be related to B in multiple ways.

Entailments involve a typing context (a list of variable typing judgments) on the left of a turnstile and a single term judgment on the right.  All the free variables on the right must appear on the left.  We read `Γ ⊢ A: B` as "a way that A relates to B in the context Γ".  More specifically, we read `x₁: X₁, ..., xₙ: Xₙ ⊢ A: B` as "for each way that x₁ relates to X₁, ..., and xₙ relates to Xₙ, a way that A relates to B".

Inference rules have a list of entailments on top and an entailment on the bottom.  All the free metavariables on the bottom must appear on the top with the same variance.  We read

  ```
  Γ ⊢ A₁: B₁    ⋯    Γ ⊢ Aₙ: Bₙ
  —————————————————————————————
  Γ ⊢ A: B
  ```

as "for each way that A₁ relates to B₁ in the context Γ, ..., and Aₙ relates to Bₙ in the context Γ, a way that A relates to B in the context Γ".

- Axiom

    Add term constructors `type^T, kind^T: 1 -> T` for each shape T in the theory.

- Start

    ```
    Γ ⊢ A: s_X
    ——————————————
    Γ, x: A ⊢ x: A
    ```

- Weakening

    ```
    Γ ⊢ A: B    Γ ⊢ C: s
    ————————————————————
    Γ, x: C ⊢ A: B
    ```
      
- Product, abstraction

    Add a term constructor `∏: T x (T -> T') -> T'` for each pair of shapes T, T' in the theory.
    We write `∏(A, λx.B)` as `∏_{x: A}.B`.

    ```
    Γ ⊢ A: s₁^T    Γ, x: A ⊢ B: s₂^{T'}
    ———————————————————————————————————
    Γ ⊢ ∏_{x: A}.B: s₂^{T -> T'}
    Γ ⊢ ∏(A, λx.B): s₂^{T -> T'}
    ```

    ```
    Γ ⊢ A: s₁^T    Γ, x: A ⊢ B: s₂^{T'}    Γ, x: A ⊢ C: B
    —————————————————————————————————————————————————————
    Γ ⊢ λx: A.C: ∏_{x: A}.B
    Γ ⊢ λx: A.C: ∏(A, λx.B)
    ```

- Product- and abstraction-like rule for each slot of ⊙ in LHS rewrites, which induces a modality for terms in that slot.   The premises are judgments assigning a type to each rewrite constructor parameter. TODO: desugar syntax below to restate substitution using ev.

  - E.g. Lambda

    - 1st slot, `beta(K, Q): App([Lam(K)], Q) ~> ev(K, Q)`

      We add a process constructor `<1>:P x (P -> P) -> P`.
      We treat `K` as `λy.L` of type `∏_{y: B}.C` and write `<1>(B, λy.C)` as `<App(-, y: B)>C`. Note that the parameters to <1> are the same as to ∏, as we expect for this modal type.

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P
      ——————————————————————————————————
      Γ ⊢ <App(-, y: B)>C: s₃^P
      Γ ⊢ <1>(B, λy.C): s₃^P
      ```

      We treat `K` as `λy.L` of type `∏_{y: B}.C` and use an uncurried version as the third premise:

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P    Γ, y: B ⊢ L: C
      ——————————————————————————————————————————————————
      Γ ⊢ Lam(λy.L) : <App(-, Q: B)>C
      Γ ⊢ Lam(λy.L) : <1>(B, λQ.C)
      ```

    - 2nd slot, `beta(K, Q): App(Lam(K), [Q]) ~> ev(K, Q)`

      We add a process constructor `<2>:P x (P -> P) x ((P -> P) -> P) -> P`.
      We write `<2>(B, λy.C, λK.D)` as `<App(Lam(K: ∏_{y: B}.C), -)>D`.

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P
      —————————————————————————————————
      Γ ⊢ <App(Lam(K: ∏_{y: B}.C), -)>D
      Γ ⊢ <2>(B, λy.C, λK.D)
      ```

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P    Γ, K: ∏_{y: B}.C ⊢ D: s₂^P    Γ ⊢ Q: B
      ——————————————————————————————————————————————————————————————————————————
      Γ ⊢ Q : <App(Lam(K: ∏_{y: B}.C), -) >D
      Γ ⊢ Q : <2>(B, λy.C, λK.D)
      ```
      
      But note that the last premise can only be derived in very restricted circumstances:

      Q: <App(Lam(K: B => C), -)>D is Q: B when D=C and Never otherwise.  So if C does not depend on a value of type B, then we can construct D=C.

      Q: <((K: ∏_{y: B}.C) -)>D is Q: B when D(λy.L) = C(z) and Never otherwise.  But since we don't know Q in advance (it's the consequent of the rule), we can't construct the third premise.

  - E.g. RHO 

    - 1st slot, `comm(x, K, Q): [x?K] | x!Q ~> ev(K, @Q)`

      We add a process constructor `<1>:N x N x P x (N -> P) -> P`.
      We treat `K` as `λy.L` of type `∏_{y: @B}.C` and write `<1>(x, A, B, λy.C)` as `< - | x: A!(Q: B) > C{@Q/y}`. Note that the parameters to <1> are the same as to ∏ except for the channel and channel type, as we expect for this modal type.

      ```    
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^P    Γ, y: @B ⊢ C: s₃^P
      ————————————————————————————————————————————————————————————
      Γ ⊢ < - | x: A ! (Q: B) > C {@Q/y}: s₃^P
      Γ ⊢ <1>(x, A, B, λy.C): s₃^P
      ```

      We treat `K` as `λy.L` of type `∏_{y: @B}.C` and use an uncurried version as the xth premise:

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^P    Γ, y: @B ⊢ C: s₃^P    Γ, y: @B ⊢ L: C
      ———————————————————————————————————————————————————————————————————————————————
      Γ ⊢ x ? (λy.L) : < - | x: A ! (Q: B) > C{@Q/y}
      Γ ⊢ x ? (λy.L) : <1>(x, A, B, λy.C)
      ```

  - 2nd slot, `comm(x, K, Q): x?K | [x!Q] ~> ev(K, @Q)`

      We add a process constructor `<2>:N x N x N x (N -> P) x ((N -> P) -> P) -> P`.
      We write `<2>(x, A, B, λy.C, λK.D)` as `< x:A ? (K: ∏_{y: B}.C) | - >D`.

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ B: s₂^N    Γ, y: B ⊢ C: s₃^P    Γ, K: ∏_{y: B}.C ⊢ D: s₃^P
      ——————————————————————————————————————————————————————————————————————————————
      Γ ⊢ < x:A ? (K: ∏_{y: B}.C) | - > D: s₃^P
      Γ ⊢ <2>(x, A, B, λy.C, λK.D): s₃^P
      
      ```

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ B: s₂^N    Γ ⊢ Q: B    Γ, y: B ⊢ C: s₃^P    Γ, K: ∏_{y: B}.C ⊢ D: s₃^P   
      —————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ x ! Q : < x: A ? (K: ∏_{y: B}.C) | - > D
      Γ ⊢ x ! Q : <2>(x, A, B, λy.C, λK.D)
      ```

- Dependent-product-like rules for term constructors taking exponential objects as parameters

  - E.g. π-calc / Rholang

      ```
      Γ ⊢ A: s₁^N    Γ, x: A ⊢ B: s₂^P
      ————————————————————————————————
      Γ ⊢ Nu(A, λx.B): s₂^P
      ```

- Abs-like rules for constructors taking exponential objects as parameters

  - E.g. π-calc / Rholang

      ```
      Γ ⊢ A: s₁^N    Γ, x: A ⊢ B: s₂^P    Γ, x: A ⊢ C: B
      ——————————————————————————————————————————————————
      Γ ⊢ New(λx.B) : Nu(A, λx.C)
      ```

- Conv-like rule

    ```
    T ∈ Ob(HC)
    ——————————————
    ⊢ ◇T ∈ Ob(HC)
    ```
    
    ```
    Γ ⊢ s(A): B    Γ ⊢ t(A): B'
    ———————————————————————————
    Γ ⊢ A: ◇B'
    ```

- App-like rules for rewrites using ev

  - E.g. RHO.  TODO: how do we check that x is the same in A's type and E's structure?

      ```
      1st slot
      
      Γ ⊢ A: < - | x: B ! (Q: C) > D    Γ ⊢ x: B    Γ ⊢ S: C
      ——————————————————————————————————————————————————————
      Γ ⊢ A | x!(S): ◇(D {S / Q})  <--- extract S using coalgebraic structure of term
      ```

      ```
      2nd slot
      
      Γ ⊢ A: < x: B ? (K: (∏_{y:C}. D)) | - > E    Γ ⊢ x: B  Γ ⊢ L: (∏_{y:C}. D)
      ——————————————————————————————————————————————————————————————————————————
      Γ ⊢ A | x?(L): ◇(E {L / K})
      ```

      A = x!c : < x: B ? (K: (∏_{y:C}. D)) | - > D(@c)
      L = λy:C. (d:D(y))
      
      x!c | x?L ~> ev(L, @c): D(@c)
      
      


- Cut-like rules...



------------------------------------------

Stuff from last version

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

- cut-like rule for each rewrite target with a use of ev on an exponental object.  TODO: express extraction from wrapper in terms of coalgebraic structure of free GSLT.

    ```
    for(chan, cont)
    For(Chan, Pi)  Pi type holds lambda Pi(L) and in the consequent we could write ev(L, @E) instead of using sugar
    ```

    ```
    Γ ⊢ for(x, K): ⟨|x:B!(Q:C)⟩D    Γ ⊢ E: C
    ———————————————————————————————————————— cut-like = target of trace, compare app
    Γ ⊢ ev(K, @E): ev(\Q.D, E)
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
