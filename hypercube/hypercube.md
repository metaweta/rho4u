Given an interactive finitely-presented GSLT T, produce new typed GSLT.

Fn sym arrows o: X1 x ... x Xn -> Y are sugar for Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ o(t1, ..., tn): Y.
Rewrite squiggly arrows ρ: os(t1, ..., tn) ~> ot(t1, ..., tn) are sugar for 
    Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ s(ρ(t1, ..., tn)) = os(t1, ..., tn)
    Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ t(ρ(t1, ..., tn)) = ot(t1, ..., tn)
Equations os(t1, ..., tn) = ot(t1, ..., tn) are sugar for 
    Γ ⊢ t1: X1 ... Γ ⊢ tn: Xn ⊨ Γ ⊢ os(t1, ..., tn) = ot(t1, ..., tn)

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
      νx.νx.P = νx.P
      
      Γ, x: N ⊢ Q1: P    Γ ⊢ Q2: P    ⊨    Γ ⊢ (νx.Q1) | Q2 = νx.(Q1 | Q2)

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
    Γ ⊢ λx.C: ∏_{x: A}.B
    Γ ⊢ λx.C: ∏(A, λx.B)
    ```
    
- Dependent-product-like and Abs-like rules for term constructors taking exponential objects as parameters.

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
      Γ ⊢ Nu(x:A.B): s₂^P
      Γ ⊢ Nu(A, λx.B): s₂^P
      ```

      ```
      Usual: x is a var of type A, Nu(x:A.B) is the type of a process that may communicate on x
      Γ ⊢ A: *^N    Γ, x: A ⊢ B: *^P
      ——————————————————————————————
      Γ ⊢ Nu(x:A.B): *^P
      Γ ⊢ Nu(A, λx.B): *^P

      Or does it use a Pi type in the premise?
      Γ ⊢ A: *^N    Γ ⊢ K: ∏x:A.*^P
      ——————————————————————————————
      Γ ⊢ Nu(K): *^P
      Γ ⊢ Nu(A, K): *^P

      Γ ⊢ A: *^N    Γ, x: A ⊢ B: *^P    Γ, x: A ⊢ C: B
      ————————————————————————————————————————————————
      Γ ⊢ New(λx.C) : Nu(A, λx.B)



      Polymorphic: x is a new type, Nu(x:*.B) is the type of a process that may use that type (including to communicate on if the For rule allows types in name position).  But it's not clear how to produce values of that new type x.  Of course, we can always create a *name* of that type via `new y:x.P`.

      Γ ⊢ *: □^N    Γ, x: * ⊢ B: *^P
      ——————————————————————————————
      Γ ⊢ Nu(x:*.B): *^P
      Γ ⊢ Nu(*, λx.B): *^P

      Γ ⊢ *: □^N    Γ, x: * ⊢ B: *^P    Γ, x: * ⊢ C: B
      ————————————————————————————————————————————————
      Γ ⊢ New(λx.C) : Nu(*, λx.B)



      Type constructor: x is a type, Nu(x:*.B) is the kind of a type-process.  Something like List[new x], a list of things of a new type.  But not clear how to create a value of that new type.  Of course, we can always create a *name* of that type via `new y:x.P`.

      Γ ⊢ *: □^N    Γ, x: * ⊢ B: □^P
      ——————————————————————————————
      Γ ⊢ Nu(x:*.B): □^P
      Γ ⊢ Nu(*, λx.B): □^P

      Γ ⊢ *: □^N    Γ, x: * ⊢ B: □^P    Γ, x: * ⊢ C: B
      ——————————————————————————————————————————————————
      Γ ⊢ New(λx.C) : Nu(*, λx.B)



      Dependent: x is a var of type A, Nu(x:A.B) is the kind of a type-process.  But what does that type process do?  ∏x:A.B is a struct type, a product of types B(x) over all x:A; a value of the struct type has a value v(x): B(x) for each x.  Σx:A.B is a union type, a sum of types B(x) over all x:A; a value of the union type has a value v(x) for some x.  What's a "Nu" over all x:A?  What's a value of the Nu type?

      Pi and sigma are right and left adjoints to change of base, respectively.
          https://ncatlab.org/nlab/show/dependent+product#definitions
          https://ncatlab.org/nlab/show/dependent+sum#definition
      Is there a similar characterization of Nu?

      Γ ⊢ A: *^N    Γ, x: A ⊢ B: □^P
      ——————————————————————————————
      Γ ⊢ Nu(x:A.B): □^P
      Γ ⊢ Nu(A, λx.B): □^P

      Γ ⊢ A: *^N    Γ, x: A ⊢ B: □^P    Γ, x: A ⊢ C: B
      ————————————————————————————————————————————————
      Γ ⊢ New(λx.C) : Nu(A, λx.B)
      ```

      ```
      Γ ⊢ A: s₁^N    Γ, x: A ⊢ B: s₂^P    Γ, x: A ⊢ C: B
      ——————————————————————————————————————————————————
      Γ ⊢ New(λx.C) : Nu(A, λx.B)
      ```
      
    - For

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^N    Γ, y: B ⊢ C: s₃^P
      ———————————————————————————————————————————————————————————
      Γ ⊢ Phi_{y: B <- x: A}.C: s₃^P
      Γ ⊢ Phi(x, A, B, λy.C): s₃^P
      ```

      ```
      Γ ⊢ A: s₁^N    Γ ⊢ x: A    Γ ⊢ B: s₂^N    Γ, y: B ⊢ C: s₃^P    Γ, y: B ⊢ D: C
      —————————————————————————————————————————————————————————————————————————————
      Γ ⊢ for(y <- x) D: Phi_(y: B <- x: A.C)
      Γ ⊢ for(x, λy.D): Phi(x, A, B, λy.C)
      ```

      Channel Polymorphic: receive on name types instead of just names

      Specializing to A=*:
      ```
      Γ ⊢ *: □^N    Γ ⊢ x: *    Γ ⊢ B: *^N    Γ, y: B ⊢ C: *^P
      ———————————————————————————————————————————————————————————
      Γ ⊢ Phi_{y: B <- x: *}.C: *^P
      Γ ⊢ Phi(x, *, B, λy.C): *^P
      ```

      ```
      Γ ⊢ *: □^N    Γ ⊢ x: *    Γ ⊢ B: *^N    Γ, y: B ⊢ C: *^P    Γ, y: B ⊢ D: C
      ——————————————————————————————————————————————————————————————————————————
      Γ ⊢ for(y <- x) D: Phi_(y: B <- x: *.C)
      Γ ⊢ for(x, λy.D): Phi(x, *, B, λy.C)
      ```

      Binder Polymorphic: able to receive types as well as names

      Specializing to B=*:
      ```
      Γ ⊢ A: *^N    Γ ⊢ x: A    Γ ⊢ *: □^N    Γ, y: * ⊢ C: *^P
      ———————————————————————————————————————————————————————————
      Γ ⊢ Phi_{y: * <- x: A}.C: *^P
      Γ ⊢ Phi(x, A, *, λy.C): *^P
      ```

      ```
      Γ ⊢ A: *^N    Γ ⊢ x: A    Γ ⊢ *: □^N    Γ, y: * ⊢ C: *^P    Γ, y: B ⊢ D: C
      —————————————————————————————————————————————————————————————————————————————
      Γ ⊢ for(y <- x) D: Phi_(y: * <- x: A.C)
      Γ ⊢ for(x, λy.D): Phi(x, A, *, λy.C)
      ```

      Binder Dependent: types compete with terms for messages

      Specializing to C=*:
      ```
      Γ ⊢ A: *^N    Γ ⊢ x: A    Γ ⊢ B: *^N    Γ, y: B ⊢ *: □^P
      ———————————————————————————————————————————————————————————
      Γ ⊢ Phi_{y: B <- x: A}.*: □^P
      Γ ⊢ Phi(x, A, B, λy.*): □^P
      ```

      ```
      Γ ⊢ A: *^N    Γ ⊢ x: A    Γ ⊢ B: *^N    Γ, y: B ⊢ *: □^P    Γ, y: B ⊢ D: *
      —————————————————————————————————————————————————————————————————————————————
      Γ ⊢ for(y <- x) D: Phi_(y: B <- x: A.*)
      Γ ⊢ for(x, λy.D): Phi(x, A, B, λy.*)
      ```

      Problem with assuming that there's a separate compile time phase:
      Assume x # R
      ((for (z <- x) P) : Q) | (R: (for(y <- x) D)) | x!(S)
                             | compile time, types always win
                             V
      ((for (z <- x) P) : Q) | (R: ◇D(@S))

      ((for (z <- x) P) : Q) | (R: (for(y <- x) D)) | x!(S)
                             | run time with type erasure, terms always win
                             V
      (P(@S)) | (R: (for(y <- x) D))
      
      For dependently typed for, where types compete with terms, there's only runtime.

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

    `◇*: P -> P`
    
    ```
    Γ ⊢ A: B
    ———————————
    Γ ⊢ A: ◇*B
    ```

    ```
    Γ ⊢ A: ◇◇*B
    —————————————
    Γ ⊢ A: ◇*B
    ```

    ```
    Γ ⊢ A: ◇*◇*B
    —————————————
    Γ ⊢ A: ◇*B
    ```

- Modalities from all process-shaped subterms of LHS of rewrites.  RHS gets turned into structural type.  Structural type has only type info in a slot when the type is a process; when it's not a process, the value is also part of the type (e.g. names in ambient/pi/RHO).  In this approach, the types aren't dependent.  For example, in the first SKI inference rule below, the term doesn't have access to z, so even though the result type does, the result type isn't actually dependent.  Also, we can't make S, x, or y depend on z because z would be free in the conclusion.

  Also 

  ```
  Γ ⊢ <K(-)>B: □
  ————————————————————
  Γ ⊢ K(<K(-)>B) = ◇B
  ```
  

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

    How do we get something like an arrow type from this?
    S: (A=>B=>C) => (A=>B) => A => C
    
    Γ ⊢ <App(-, A)><App(-, B)>C: *^P    Γ ⊢ x: <App(-, A)><App(-, B)>C    Γ ⊢ <App(-, A)>B: *^P    Γ ⊢ y: <App(-, A)>B    Γ ⊢ A: *^P
    ————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>App(App(<App(-, A)><App(-, B)>C, A), <App(-, A)>B)
    ———————————————————————————————————————————————————————————————————————————————————————
    Γ ⊢ App(App(S, x), y): <App(-, z: C)>App(App(<App(-, A)><App(-, B)>C, A), <App(-, A)>B)

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

  - What about ones where there's an exponential in the context?  E.g. Lambda `β: App(Lam(λx.C), D) ~> ev(λx.C, D)`.  Here we can put x into the context for B and C.  For example, suppose that A is bool, B is `[true, int] + [false, string]` (existential type).  Then ev(λx.B, D) will be either int or string.  But bool might be a subset of the values that we could put in the second slot to get one of those results, so the inference rule ends up weakening the type of D.  That seems OK.

    ```
    Γ ⊢ A: s^P    Γ, x: A ⊢ B: s^P    Γ, x: A ⊢ C: B    Γ ⊢ D: A
    ————————————————————————————————————————————————————————————
    Γ ⊢ D: <App(Lam(λx.C: ∏x:A.B), -)>ev(λx.B, D)
    Γ ⊢ D: <β>(A, λx.C, λx.B, D)
    ```

- Conv can be used in any modality context:

    ```
    Γ ⊢ A: ◇B    Γ ⊢ ρ: B ~> B'
    —————————————————————————————
    Γ ⊢ A: ◇◇B'
    ```

    ```
    Γ ⊢ A: <B>C    Γ ⊢ ρ: C ~> C'
    —————————————————————————————
    Γ ⊢ A: <B>◇C'
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

- Later: Cut-like rules for each rewrite target with a use of ev on an exponental object.  TODO: express extraction from wrapper in terms of coalgebraic structure of free GSLT.

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
