Given an interactive finitely-presented GSLT T, produce new typed GSLT.

- E.g. RHO calculus

    ```
    shapes
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
    shapes
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

- E.g. SKI

    ```
    shapes
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.

    fn syms
      App: P x P -> P
      S, K, I: 1 -> P
      S1: P -> P
      S2: P x P -> P
      K1: P -> P
    
    eqns
      // V = P from above
    
    rewrites
      σ1: P -> R
      σ1: App(S, x) ~> S1(x)
      
      σ2: P x P -> R
      σ2: App(S1(x) y) ~> S2(x, y)
      
      σ3: P x P x P -> R
      σ3: App(S2(x, y) z) ~> ((x z) (y z))
      
      κ1: P -> R
      κ1: App(K, x) ~> K1(x)
      
      κ2: P x P -> R
      κ2: App(K1(x), y) ~> x
            
      ι1: P -> R
      ι1: App(I, x) ~> x
      
      head: R x P -> R
      head: App(s(E), Q) ~> App(t(E), Q)
    ```

- E.g. Ambient

    ```
    shapes
      // Automatically have R, V, s,t: R -> V.
      P // First shape gets set equal to V as equation of identity morphisms.
      N
      M

    fn syms
      ν: (N -> P) -> P
      0: 1 -> P
      |: P x P -> P
      !: P -> P
      []: N x P -> P
      .: M x P -> P
      in, out, open: N -> M

    eqns
      comm. mon.
      νx.νy.P = νy.νx.P
      νv.νx.P = νx.P

    rewrites
      expand: P -> R
      expand: !Q ~> Q | !Q

      ambient: N x R -> R
      ambient: n[s(E)] ~> n[t(E)]

      in: N x N x P x P x P -> R
      in: n[in m.Q | R] | m[S] ~> m[n[Q | R] | S]

      out: N x N x P x P x P -> R
      out: m[n[out m:Q | R] | S] ~> n[Q | R] | m[S]

      open: N x P x P -> R
      open: open m.P | m[Q] ~> P | Q
    ```

  - E.g. Rule 110?

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
    
- Dependent-product-like and Abs-like rules for term constructors taking exponential objects as parameters

  - E.g. λ-calc

      ```
      Γ ⊢ A: s₁^P    Γ, x: A ⊢ B: s₂^P
      ————————————————————————————————
      Γ ⊢ Pi(A, λx.B): s₂^P
      ```

      ```
      Γ ⊢ A: s₁^P    Γ, x: A ⊢ B: s₂^P    Γ, x: A ⊢ C: B
      ——————————————————————————————————————————————————
      Γ ⊢ Lam(λx.C): Pi(A, λx.B)
      ```

  - E.g. π-calc / Rholang

    - New: Nu
      ```
      Γ ⊢ A: s₁^N    Γ, x: A ⊢ B: s₂^P
      ————————————————————————————————
      Γ ⊢ Nu(A, λx.B): s₂^P
      ```

      ```
      Γ ⊢ A: s₁^N    Γ, x: A ⊢ B: s₂^P    Γ, x: A ⊢ C: B
      ——————————————————————————————————————————————————
      Γ ⊢ New(λx.B) : Nu(A, λx.C)
      ```

    - For

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^P    Γ, y: B ⊢ C: s₃^P
      ———————————————————————————————————————————————————————————
      Γ ⊢ Pi(x, A, B, λy.C)
      Γ ⊢ Pi_{y: B <- x: A}.C
      ```
      
      ```
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^P    Γ, y: B ⊢ C: s₃^P    Γ, y: B ⊢ D: C
      —————————————————————————————————————————————————————————————————————————————
      Γ ⊢ for(y <- x) D: Pi_(y: B <- x: A.C)
      Γ ⊢ for(x, λy.D): Pi(x, A, B, λy.C)
      ```

- Conv-like rule

    `◇: P -> P`

    ```
    Γ ⊢ A: s
    ——————————
    Γ ⊢ ◇A: s
    ```
    
    ```
    Γ ⊢ A: s    Γ ⊢ B: A    Γ ⊢ ρ: B ~> B'    Γ ⊢ B': A'
    ————————————————————————————————————————————————————
    Γ ⊢ B: ◇A'
    ```

- Modalities from all process subterms of LHS of rewrites.  RHS gets turned into structural type.  Structural type has only type info in a slot when the type is a process; when it's not a process, the value is also part of the type (e.g. names in ambient/pi/RHO).

  - E.g. SKI `σ: App(App(App(S, x), y), z) ~> App(App(x, z), App(y, z)`
                               `A   B   C`

    ```
    Γ ⊢ A: s^P    Γ ⊢ x: A    Γ ⊢ B: s^P    Γ ⊢ y: B    Γ ⊢ C: s^P
    ——————————————————————————————————————————————————————————————
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>App(App(A, C), App(B, C))
    
    Γ ⊢ A: s^P    Γ ⊢ x: A    Γ ⊢ B: s^P    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————————
    Γ ⊢ App(S, x): <App(App(-, y: B), z: C)>App(App(A, C), App(B, C))
    
    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ ⊢ C: s^P
    ————————————————————————————————————————————————————————————————————
    Γ ⊢ S: <App(App(App(-, x: A), y: B), z: C)>App(App(A, C), App(B, C))
    
    Γ ⊢ A: s^P    Γ ⊢ x: A    Γ ⊢ B: s^P    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————————
    Γ ⊢ x: <App(App(App(S, -), y: B), z: C)>App(App(A, C), App(B, C))

    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ ⊢ y: B    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————————
    Γ ⊢ y: <App(App(App(S, x: A), -), z: C)>App(App(A, C), App(B, C))

    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ ⊢ C: s^P    Γ ⊢ z: C
    —————————————————————————————————————————————————————————————————
    Γ ⊢ z: <App(App(App(S, x: A), y: B), -)>App(App(A, C), App(B, C))
    ```

  - E.g. Ambient `in: n[ in m.Q | R ] | m[ S ] ~> m[ n[ Q | R ] | S ]`
                     `A     B C   D     B  E`

    ```
    Γ ⊢ A: s^N    Γ ⊢ m: A    Γ ⊢ B: s^N    Γ ⊢ n: B    Γ ⊢ C: s^P    Γ ⊢ Q: C    Γ ⊢ D: s^P    Γ ⊢ R: D    Γ ⊢ E: s^P
    ——————————————————————————————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ n[ in m.Q | R ]: < - | (m: A)[ S: E ]>(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ m: A    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ D: s^P    Γ ⊢ E: s^P    Γ ⊢ S: E
    ——————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ m[ S ]: < (n: B)[ in (m: A).(Q: C) | (R: D) ] | ->(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ Q: C    Γ ⊢ D: s^P    Γ ⊢ E: s^P
    ————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ Q: <(n: B)[ in (m: A).- | (R: D) ] | (m: A)[ S: E ]>(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ D: s^P    Γ ⊢ R: D    Γ ⊢ E: s^P
    ————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ R: <(n: B)[ in (m: A).(Q: C) | - ] | (m: A)[ S: E ]>(m: A)[(n: B)[ C | D ] | E ]

    Γ ⊢ A: s^N    Γ ⊢ B: s^N    Γ ⊢ C: s^P    Γ ⊢ D: s^P    Γ ⊢ E: s^P    Γ ⊢ S: E
    ——————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ S: <(n: B)[ in (m: A).(Q: C) | (R: D) ] | (m: A)[ - ]>(m: A)[(n: B)[ C | D ] | E ]
    ```

  - What about ones where there's an exponential in the context?  E.g. Lambda `β: App(Lam(λx.C), D) ~> ev(λx.C, D)`

    ```
    Γ ⊢ A: s^P    Γ ⊢ B: s^P    Γ, x: A ⊢ C: B    Γ ⊢ D: A
    ——————————————————————————————————————————————————————
    Γ ⊢ D: <App(Lam(λx:A.C), -)>B                        // B is structural type of ev(λx.C, D)?
    ```

- Conv in modality context

    ```
    Γ ⊢ A: <B>C    Γ ⊢ ρ: C ~> C'
    —————————————————————————————
    Γ ⊢ A: <B>◇C
    ```
    
  - E.g. SKI

    ```
    Γ ⊢ K: s^P    Γ ⊢ K: K    Γ ⊢ K: s^P    Γ ⊢ K: K    Γ ⊢ C: s^P
    —————————————————————————————————————————————————————————————— modality
    Γ ⊢ App(App(S, K), K): <App(-, z: C)>App(App(K, C), App(K, C))    Γ ⊢ κ(C, App(K, C): App(App(K, C), App(K, C)) ~> C
    ———————————————————————————————————————————————————————————————————————————————————————————————————————————————————— conv
    Γ ⊢ App(App(S, K), K): <App(-, z: C)>◇C
    ```

- App-like rules for rewrites using ev

  - E.g. RHO.

      ```
      Γ ⊢ A: Pi(x, B, C, λQ.D)          Γ ⊢ x: B    Γ ⊢ S: C    Γ ⊢ λQ.D: ∏(C, λQ.s)
      Γ ⊢ A: < - | x: B ! (Q: C) > D    Γ ⊢ x: B    Γ ⊢ S: C    Γ ⊢ λQ.D: ∏_{Q: C}.s
      ——————————————————————————————————————————————————————————————————————————————
      Γ ⊢ A | x!(S): ◇(D {S / Q})
      Γ ⊢ A | x!(S): ◇ev(λQ.D, S)
      ```

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


- Product- and abstraction-like rule for each slot of ⊙ in LHS rewrites, which induces a modality for terms in that slot.   The premises are judgments assigning a type to each rewrite constructor parameter. TODO: desugar syntax below to restate substitution using ev.

  - E.g. Ambient.

    - 1st slot of in, `in(n, m, Q, R, S): {n[in m.Q | R]} | m[S] ~> m[n[Q | R] | S]`
    
      We add a process constructor `<in1>:N x N x P x (P -> P) -> P`.
      We write `<in1>(m, A, B, λS.C)` as `< - | (m: A)[S: B] >C`.

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ m: A    Γ ⊢ B: s₂^P    Γ, S: B ⊢ C: s₃^P
      ———————————————————————————————————————————————————————————
      Γ ⊢ < - | (m: A)[S: B] >C: s₃^P
      Γ ⊢ <in1>(m, A, B, λS.C): s₃^P
      ```

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ m: A    Γ ⊢ B: s₂^P    Γ, S: B ⊢ C: s₃^P    Γ ⊢ D: s₄^N    Γ ⊢ n: D    Γ ⊢ E: s₅^P    Γ ⊢ Q: E    Γ ⊢ F: s₆^P    Γ ⊢ R: F
      ————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ n[in m.Q | R] : < - | (m: A)[S: B] >C
      Γ ⊢ n[in m.Q | R] : <in1>(m, A, B, λS.C)
      ```

      Problem with this rule: no relation between types involved in the premises for constructing the term and types in the dependent product.


    - 2nd slot of in, `in(n, m, Q, R, S): n[in m.Q | R] | {m[S]} ~> m[n[Q | R] | S]`
    
      We add a process constructor `<in2>: N x N x N x (N x P x P -> P) -> P`.
      We write `<in2>(A, m, B, C, D, λnQR.C)` as `< (n: A)[in (m: B).(Q: C) | (R: D)] | - >E`.

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ B: s₂^N    Γ ⊢ m: B    Γ ⊢ C: s₃^P    Γ ⊢ D: s₄^P    Γ, n: A, Q: C, R: D ⊢ E: s₅^P
      —————————————————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ < (n: A)[in (m: B).(Q: C) | (R: D)] | - >E: s₅^P
      Γ ⊢ <in2>(A, m, B, C, D, λnQR.E): s₅^P
      ```

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ B: s₂^N    Γ ⊢ m: B    Γ ⊢ C: s₃^P    Γ ⊢ D: s₄^P    Γ, n: A, Q: C, R: D ⊢ E: s₅^P    Γ ⊢ F: s₆^P    Γ ⊢ S: F
      ————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ m[S]: < (n: A)[in (m: B).(Q: C) | (R: D)] | - >E
      Γ ⊢ m[S]: <in2>(A, m, B, C, D, λnQR.E)
      ```

      Problem with this rule: no relation between types involved in the premises for constructing the term and types in the dependent product.
 
  - E.g. SKI

    - 1st slot of σ1, `σ11:App([S], A) ~> S1(A)`
    
      We add a process constructor `<σ11>: P x (P -> P) -> P`.
      We write `<σ11>(B, λA.C)` as `<σ1.App(-, A: B)>C`.
      
      ```
      Γ ⊢ B: s₁^P    Γ, A: B ⊢ C: s₂^P
      ————————————————————————————————
      Γ ⊢ <σ1.App(-, A: B)>C: s₂^P
      Γ ⊢ <σ11>(B, λA.C): s₂^P
      ```
      
      ```
      Γ ⊢ B: s₁^P    Γ, A: B ⊢ C: s₂^P    ???
      ———————————————————————————————————————
      Γ ⊢ ???: <σ1.App(-, A: B)>C
      ```

  - E.g. Lambda. Trouble in second slot because one shape in ev and therefore one type in context (input to pi type) is contravariant.

    - 1st slot, `beta(K, Q): App([Lam(K)], Q) ~> ev(K, Q)`

      We add a process constructor `<1>:P x (P -> P) -> P`.
      We write `<1>(B, λy.C)` as `<App(-, y: B)>C`. Note that the parameters to <1> are the same as to ∏, as we expect for this modal type.

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P
      ——————————————————————————————————
      Γ ⊢ <App(-, y: B)>C: s₃^P
      Γ ⊢ <1>(B, λy.C): s₃^P
      ```

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P    Γ ⊢ K: ∏_{y: B}.C
      —————————————————————————————————————————————————————
      Γ ⊢ Lam(K) : <App(-, y: B)>C
      Γ ⊢ Lam(K) : <1>(B, λy.C)
      ```

    - 2nd slot, `beta(K, Q): App(Lam(K), [Q]) ~> ev(K, Q)`

      We add a process constructor `<2>:P x (P -> P) x ((P -> P) -> P) -> P`.
      We write `<2>(B, λy.C, λK.D)` as `<App(Lam(K: ∏_{y: B}.C), -)>D`.

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P    Γ, K: ∏_{y: B}.C ⊢ D: s₃^P
      ——————————————————————————————————————————————————————————————
      Γ ⊢ <App(Lam(K: ∏_{y: B}.C), -)>D: s₃^P
      Γ ⊢ <2>(B, λy.C, λK.D): s₃^P
      ```
      
      B = bool
      C(y) = bool
      K = a function from bool to bool
      D(K) = if (ev(K, true)) then string else int
      premises are met, so we can construct the modal type
      

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P    Γ, K: ∏_{y: B}.C ⊢ D: s₃^P    Γ, K: ∏_{y: B}.C ⊢ E: D
      —————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ E: <App(Lam(K: ∏_{y: B}.C), -)>D
      Γ ⊢ E: <2>(B, λy.C, λK.D)
      ```

      E(K) = if (ev(K, true)) then "hi" else 5
      
      But in the consequent, K is free in E, so the rule doesn't parse.  If we keep it as part of the typing context, then the rule isn't sound:

      ```
      Γ ⊢ B: s₁^P    Γ, y: B ⊢ C: s₂^P    Γ, K₁: ∏_{y: B}.C ⊢ D: s₃^P    Γ, K₂: ∏_{y: B}.C ⊢ E: D
      ———————————————————————————————————————————————————————————————————————————————————————————
      Γ, K₂: ∏_{y: B}.C ⊢ E: <App(Lam(K₁: ∏_{y: B}.C), -)>D
      Γ, K₂: ∏_{y: B}.C ⊢ E: <2>(B, λy.C, λK₁.D)
      ```

      App(Lam(K₁, E) ~> ev(K₁, E), but E is not bool, so it'll be some implementation-dependent type, not necessarily D.

      Here are sound restrictions, but I don't know how to derive them:
      
      ```
      Γ ⊢ B: s₁^P    Γ ⊢ C: s₂^P
      ———————————————————————————————————
      Γ ⊢ <App(Lam(K: B => C), -)>C: s₂^P
      Γ ⊢ <2>(B, C): s₂^P
      ```

      ```
      Γ ⊢ B: s₁^P    Γ ⊢ C: s₂^P    Γ ⊢ Q: B
      ——————————————————————————————————————
      Γ ⊢ Q: <App(Lam(K: B => C), -)>C
      Γ ⊢ Q: <2>(B, C)
      ```
      
      - call/cc

        Suppose we capture the current continuation via Q = (call/cc S). 
        
        ```
        App(Lam(K: ∏_{y: B}.C), (call/cc S)) = ev(S, λb.App(Lam(K: ∏_{y: B}.C), b))
        ```
        
        ```
        Γ, K: ∏_{y: B}.C ⊢ D: s^P    Γ ⊢ S: ∏_{z: ∏_{b: B}.◇C{b/y}}.???
        ————————————————————————————————————————————————————
        Γ ⊢ (call/cc S) : <App(Lam(K: ∏_{y: B}.C), -) >D
        Γ ⊢ (call/cc S) : <2>(B, λy.C, λK.D)
        ```
        
        Note however that call/cc captures the whole context, not just up to the App.
        Maybe call-with-current-delimited-continuation?

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
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^N    Γ, y: B ⊢ C: s₃^P    Γ, K: ∏_{y: B}.C ⊢ D: s₃^P
      —————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ < x:A ? (K: ∏_{y: B}.C) | - > D: s₃^P
      Γ ⊢ <2>(x, A, B, λy.C, λK.D): s₃^P
      
      ```

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^N    Γ, y: B ⊢ C: s₃^P    Γ, K: ∏_{y: B}.C ⊢ D: s₃^P    Γ ⊢ Q: B
      —————————————————————————————————————————————————————————————————————————————————————————————————————
      Γ ⊢ x ! Q : < x: A ? (K: ∏_{y: B}.C) | - > D
      Γ ⊢ x ! Q : <2>(x, A, B, λy.C, λK.D)
      ```

      This has the same problem as the analogous construction in λ-calculus.



K( P( x, Q ), E( x’, F ) ) -> K( Qu, Fv )
