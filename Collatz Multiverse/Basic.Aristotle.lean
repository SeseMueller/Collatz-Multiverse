/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4f5752ee-8169-4046-a039-b78a5ec0e308

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem shapeUniversesWithPowerOfTwoMultipliersAreBounded (u : CollatzUniverse)
(h : isShapeUniverse u) (m : ∃ k : ℕ, u.multiplier = 2 ^ k) : isBounded u

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Use
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Logic.Function.Iterate

import Aesop

-- import Batteries.Tactic.GeneralizeProofs

-- namespace Harmonic.GeneralizeProofs
-- -- Harmonic `generalize_proofs` tactic

-- open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
-- def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
--   let mut e := e
--   let mut fvars' : List Expr := []
--   for i' in [0:fvars.size] do
--     let fvar := fvars[fvars.size - i' - 1]!
--     e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
--     match e with
--     | .letE _ _ v b _ => e := b.instantiate1 v
--     | .lam _ _ _b _ => fvars' := fvar :: fvars'
--     | _ => unreachable!
--   return (fvars'.toArray, e)

-- partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
--   if (← read).depth ≤ (← read).config.maxDepth then
--     MAbs.withRecurse <| visit (← instantiateMVars e) ty?
--   else return e
-- where
--   visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
--     if (← read).config.debug then
--       if let some ty := ty? then
--         unless ← isDefEq (← inferType e) ty do
--           throwError "visit: type of{indentD e}\nis not{indentD ty}"
--     if e.isAtomic then
--       return e
--     else
--       checkCache (e, ty?) fun _ ↦ do
--         if ← isProof e then
--           visitProof e ty?
--         else
--           match e with
--           | .forallE n t b i =>
--             withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
--               mkForallFVars #[x] (← visit (b.instantiate1 x) none)
--                 (usedOnly := false) (usedLetOnly := false)
--           | .lam n t b i => do
--             withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
--               let ty'? ←
--                 if let some ty := ty? then
--                   let .forallE _ _ tyB _ ← pure ty
--                     | throwError "Expecting forall in abstractProofs .lam"
--                   pure <| some <| tyB.instantiate1 x
--                 else
--                   pure none
--               mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?)
--                 (usedOnly := false) (usedLetOnly := false)
--           | .letE n t v b _ =>
--             let t' ← visit t none
--             withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
--               mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
--           | .app .. =>
--             e.withApp fun f args ↦ do
--               let f' ← visit f none
--               let argTys ← appArgExpectedTypes f' args ty?
--               let mut args' := #[]
--               for arg in args, argTy in argTys do
--                 args' := args'.push <| ← visit arg argTy
--               return mkAppN f' args'
--           | .mdata _ b  => return e.updateMData! (← visit b ty?)
--           | .proj _ _ b => return e.updateProj! (← visit b none)
--           | _           => unreachable!
--   visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
--     let eOrig := e
--     let fvars := (← read).fvars
--     let e := e.withApp' fun f args => f.beta args
--     if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
--     let e ←
--       if let some ty := ty? then
--         if (← read).config.debug then
--           unless ← isDefEq ty (← inferType e) do
--             throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
--         mkExpectedTypeHint e ty
--       else pure e
--     if (← read).config.debug then
--       unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
--         throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
--           fvars: {fvars}"
--     let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
--     if !(← read).config.abstract && !fvars'.isEmpty then
--       return eOrig
--     if (← read).config.debug then
--       unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
--         throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
--           fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
--     let pfTy ← instantiateMVars (← inferType pf)
--     let pfTy ← abstractProofs' pfTy none
--     if let some pf' ← MAbs.findProof? pfTy then
--       return mkAppN pf' fvars'
--     MAbs.insertProof pfTy pf
--     return mkAppN pf fvars'
-- partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
--     (k : Array Expr → Array Expr → Expr → MGen α) :
--     MGen α := do
--   let propToFVar := (← get).propToFVar
--   let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
--   let rec
--     go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
--         (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
--       if h : i < generalizations.size then
--         let (ty, pf) := generalizations[i]
--         let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
--         withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
--           go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
--             (proofToFVar := proofToFVar.insert pf fvar)
--             (propToFVar := propToFVar.insert ty fvar)
--       else
--         withNewLocalInstances fvars 0 do
--           let e' := e.replace proofToFVar.get?
--           modify fun s => { s with propToFVar }
--           k fvars pfs e'
--   go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

-- partial def generalizeProofsCore'
--     (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
--     MGen (Array Expr × MVarId) := go g 0 #[]
-- where
--   go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
--     let tag ← g.getTag
--     if h : i < rfvars.size then
--       let fvar := rfvars[i]
--       if fvars.contains fvar then
--         let tgt ← instantiateMVars <| ← g.getType
--         let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
--         if ← pure tgt.isLet <&&> Meta.isProp ty then
--           let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
--           let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
--           g.assign <| .app g' tgt.letValue!
--           return ← go g'.mvarId! i hs
--         if let some pf := (← get).propToFVar.get? ty then
--           let tgt' := tgt.bindingBody!.instantiate1 pf
--           let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
--           g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
--           return ← go g'.mvarId! (i + 1) hs
--         match tgt with
--         | .forallE n t b bi =>
--           let prop ← Meta.isProp t
--           withGeneralizedProofs' t none fun hs' pfs' t' => do
--             let t' := t'.cleanupAnnotations
--             let tgt' := Expr.forallE n t' b bi
--             let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
--             g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false)
--               (usedLetOnly := false)) pfs'
--             let (fvar', g') ← g'.mvarId!.intro1P
--             g'.withContext do Elab.pushInfoLeaf <|
--               .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
--             if prop then
--               MGen.insertFVar t' (.fvar fvar')
--             go g' (i + 1) (hs ++ hs')
--         | .letE n t v b _ =>
--           withGeneralizedProofs' t none fun hs' pfs' t' => do
--             withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
--               let tgt' := Expr.letE n t' v' b false
--               let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
--               g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false)
--                 (usedLetOnly := false)) (pfs' ++ pfs'')
--               let (fvar', g') ← g'.mvarId!.intro1P
--               g'.withContext do Elab.pushInfoLeaf <|
--                 .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
--               go g' (i + 1) (hs ++ hs' ++ hs'')
--         | _ => unreachable!
--       else
--         let (fvar', g') ← g.intro1P
--         g'.withContext do Elab.pushInfoLeaf <|
--           .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
--         go g' (i + 1) hs
--     else if target then
--       withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
--         let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
--         g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
--         return (hs ++ hs', g'.mvarId!)
--     else
--       return (hs, g)

-- end GeneralizeProofs

-- open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
-- partial def generalizeProofs'
--     (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
--     MetaM (Array Expr × MVarId) := do
--   let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
--   g.withContext do
--     let s := { propToFVar := ← initialPropToFVar }
--     GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

-- elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
--     hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
--   let config ← elabConfig (mkOptionalNode config?)
--   let (fvars, target) ←
--     match expandOptLocation (Lean.mkOptionalNode loc?) with
--     | .wildcard => pure ((← getLCtx).getFVarIds, true)
--     | .targets t target => pure (← getFVarIds t, target)
--   liftMetaTactic1 fun g => do
--     let (pfs, g) ← generalizeProofs' g fvars target config
--     g.withContext do
--       let mut lctx ← getLCtx
--       for h in hs, fvar in pfs do
--         if let `(binderIdent| $s:ident) := h then
--           lctx := lctx.setUserName fvar.fvarId! s.getId
--         Expr.addLocalVarInfoForBinderIdent fvar h
--       Meta.withLCtx lctx (← Meta.getLocalInstances) do
--         let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
--         g.assign g'
--         return g'.mvarId!

-- end Harmonic

-- Inspired by CaryKH's Collatz Multiverse video: https://www.youtube.com/watch?v=n63FBYqj98E
-- In this repositiory, I want to formalize and prove some of the claims made in that video.

-- We define a Collatz Universe to be an object that contains two Natural Numbers as parameters.
-- It is used as a data structure to decide what to do in the Collatz function, specifically
-- in the odd case.
-- The multiplier (standard: 3) will be what the number is multiplied by in the odd case,
-- and the adder (standard: 1) will be what is added to the number in the odd case.
structure CollatzUniverse where
  multiplier : ℕ
  adder : ℕ
deriving Repr

def applyCollatz (u : CollatzUniverse) (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    n / 2
  else
    u.multiplier * n + u.adder

-- We are interested in the repeated application of this function,
-- so we define a function that applies the Collatz function k times to a number n.
def applyCollatzKTimes (u : CollatzUniverse) (n : ℕ) (k : ℕ) : ℕ :=
  if k = 0 then
    n
  else
    applyCollatzKTimes u (applyCollatz u n) (k - 1)

-- We call a Collatz Universe a "Hub-and-Spoke" universe if the multiplier is 0.
-- These Universes are characterized by the fact that all odd numbers are sent to the same number
-- (the adder, and, visually, the "hub").
def isHubAndSpoke (u : CollatzUniverse) : Prop :=
  u.multiplier = 0

-- Theorem: In a Hub-and-Spoke universe, all odd numbers are sent to the adder of the universe.
theorem oddNumbersSentToSameNumber (u : CollatzUniverse) (n : ℕ) (h : isHubAndSpoke u)
(hn : n % 2 = 1) : applyCollatz u n = u.adder := by
  unfold applyCollatz
  unfold isHubAndSpoke at h
  rw [h, hn]
  simp

-- Maybe I can also prove that in a Hub-and-Spoke universe, all numbers eventually end up
-- at the adder, but I will save that for later.

-- TODO: maybe prove the bi-angle or tri-angle nature of hub-and-spoke universes
-- with an adder which is a power of 2?

-- TODO: Prove the statement about period doubling in the Hub-and-Spoke universes


-- We call a universe with an adder of 0 a "Shape Universe", since all multipliers which are
-- a power of 2 give rise to shapes with log_2(n) sides (or more precisely, edges).
def isShapeUniverse (u : CollatzUniverse) : Prop :=
  u.adder = 0

-- We call a universe "bounded", if for all nubers, there exists a k and N such that
-- applying the Collatz function k times to the number results in a number
-- less than or equal to N.
def isBounded (u : CollatzUniverse) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ k : ℕ, applyCollatzKTimes u n k ≤ N

-- This means that all numbers eventually end up in a cycle, and that there are no
-- divergent trajectories. However, it does not limit the size or number of the cycles.
-- Also note that this does not mean that the cycle needs to include, or even include
-- or contain lower numbers than the starting number.

-- It is enough to show that there is some k for which all n do not grow.
-- theorem isBoundedIfPathGoesLower: (∀ n : ℕ, ∃ k : ℕ, applyCollatzKTimes u n k ≤ n) →
-- isBounded u := by
--   simp only [isBounded]
--   intro h n
--   specialize h n
--   obtain ⟨k, hk⟩ := h
--   sorry

-- We can show that the Shape Universes with a multiplier which is a power of 2 are bounded.
noncomputable section AristotleLemmas

lemma applyCollatzKTimes_zero (u : CollatzUniverse) (n : ℕ) : applyCollatzKTimes u n 0 = n := by
  unfold applyCollatzKTimes; simp

/-
If we start with `2^k * n`, applying Collatz `k` times results in `n`.
This is because `2^k * n` is even, so we divide by 2 repeatedly.
-/
lemma applyCollatzKTimes_power_of_two_mul (u : CollatzUniverse) (n k : ℕ) :
applyCollatzKTimes u (2^k * n) k = n := by
  have h_div : ∀ m : ℕ, applyCollatzKTimes u (2 ^ m * n) m = n := by
    -- intro m; induction m <;> simp_all +decide [Nat.pow_zero, Nat.one_mul] ;
    intro m; induction m;
    · unfold applyCollatzKTimes; simp_all only [↓reduceIte, Nat.pow_zero, Nat.one_mul];
    · -- By definition of applyCollatzKTimes, we can rewrite the left-hand side.
      expose_names;
      have h_apply : applyCollatzKTimes u (2 * (2 ^ ‹_› * n)) (‹_› + 1) =
      applyCollatzKTimes u (applyCollatz u (2 * (2 ^ ‹_› * n))) ‹_› := by
        rw [applyCollatzKTimes];
        rfl
      -- Aristotle didn't give me the 100% correct proof here for some reason,
      --- my environment is probably weird.
      have: (2 ^ (n_1 + 1) * n) = (2 * (2 ^ n_1 * n)) := by
        rw [Nat.pow_succ']
        exact Nat.mul_assoc 2 (2 ^ n_1) n
      convert_to applyCollatzKTimes u (2 * (2 ^ n_1 * n)) (n_1 + 1) = n
      · exact
        Nat.succ_inj.mp
          (congrArg Nat.succ (congrFun (congrArg (applyCollatzKTimes u) this) (n_1 + 1)))
      rw [h_apply];
      unfold applyCollatz; aesop;
  exact h_div k

/-
In a Shape Universe with multiplier `2^m`, applying the Collatz function to an odd number `n`
results in `2^m * n`.
-/
lemma shape_odd_step (u : CollatzUniverse) (m : ℕ) (h_shape : isShapeUniverse u)
  (h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : n % 2 = 1) : applyCollatz u n = 2^m * n := by
  unfold applyCollatz;
  simp_all only [Nat.succ_ne_self, ↓reduceIte, Nat.add_eq_left]
  exact h_shape;

/-
In a Shape Universe with multiplier `2^m`, applying the Collatz function `m+1` times
to an odd number `n` returns `n`. This is because the first step multiplies by `2^m`
(since adder is 0), and the next `m` steps divide by 2.
-/
lemma shape_odd_return (u : CollatzUniverse) (m : ℕ) (h_shape : isShapeUniverse u)
(h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : n % 2 = 1) :
applyCollatzKTimes u n (m + 1) = n := by
  convert applyCollatzKTimes_power_of_two_mul u n m using 1;
  rw [ show applyCollatzKTimes u n ( m + 1 ) = applyCollatzKTimes u ( applyCollatz u n ) m
    from ?_, shape_odd_step u m h_shape h_mult n h_odd ];
  -- By definition of applyCollatzKTimes, we can rewrite the left-hand side as the right-hand side.
  rw [applyCollatzKTimes];
  rfl

/-
Applying Collatz `a + b` times is the same as applying it `a` times,
and then applying it `b` times to the result.
-/
lemma applyCollatzKTimes_add (u : CollatzUniverse) (n a b : ℕ) : applyCollatzKTimes u n (a + b) =
applyCollatzKTimes u (applyCollatzKTimes u n a) b := by
  -- By definition of `applyCollatzKTimes`, we can rewrite the right-hand side of the equation
  -- using the recursive definition.
  have h_apply : ∀ n k, applyCollatzKTimes u n k = Nat.iterate (applyCollatz u) k n := by
    intro n k; induction k <;>
      simp_all +decide only [Function.iterate_zero, id_eq, Function.iterate_succ_apply'] ;
    · unfold applyCollatzKTimes; simp_all only [↓reduceIte];
    · -- By definition of `applyCollatzKTimes`, we have
      -- `applyCollatzKTimes u n (k + 1) = applyCollatzKTimes u (applyCollatz u n) k`.
      have h_def : ∀ n k, applyCollatzKTimes u n (k + 1) =
      applyCollatzKTimes u (applyCollatz u n) k := by
        intros n k
        rw [applyCollatzKTimes];
        rfl;
      -- By induction on $k$, we can show that applyCollatzKTimes u n k is equal to the iterate
      -- of applyCollatz u applied $k$ times to $n$.
      have h_ind : ∀ k n, applyCollatzKTimes u n k = Nat.iterate (applyCollatz u) k n := by
        intro k; induction k <;>
          simp_all +decide only [Function.iterate_zero, id_eq, Function.iterate_succ_apply'] ;
        · unfold applyCollatzKTimes; aesop;
        · (expose_names; exact fun n ↦ Function.iterate_succ_apply' (applyCollatz u) n_3 n);
      rw [ h_ind, Function.iterate_succ_apply' ];
  rw [ h_apply, h_apply, h_apply, Function.iterate_add_apply ];
  rw [ ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply ]

/-
In a Shape Universe, if we start at `2^m * n`, the next `m` steps will just divide by 2 repeatedly,
yielding `2^(m-k) * n` at step `k`.
-/
-- This doesn't require a shape universe.
lemma shape_cycle_descent (u : CollatzUniverse) (m : ℕ) --(h_shape : isShapeUniverse u)
(h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : n % 2 = 1) :
  ∀ k ≤ m, applyCollatzKTimes u (2^m * n) k = 2^(m-k) * n := by
    intro k hk_le_m
    have h_ind : ∀ k ≤ m, applyCollatzKTimes u (2^m * n) k =
    applyCollatzKTimes u (2^(m-k) * n) 0 := by
      intros k hk_le_m
      have h_ind_step : ∀ k ≤ m, applyCollatzKTimes u (2^m * n) (k + 1) =
      applyCollatzKTimes u (2^(m-k) * n) 1 := by
        intros k hk_le_m
        have h_ind_step : applyCollatzKTimes u (2^m * n) (k + 1) =
        applyCollatzKTimes u (applyCollatzKTimes u (2^m * n) k) 1 := by
          exact applyCollatzKTimes_add u (2 ^ m * n) k 1;
        convert h_ind_step using 2;
        rw [ show 2 ^ m * n = 2 ^ k * ( 2 ^ ( m - k ) * n ) by
          rw [ ← Nat.mul_assoc, ← Nat.pow_add, add_tsub_cancel_of_le hk_le_m ],
            applyCollatzKTimes_power_of_two_mul ];
      cases k <;> simp_all +decide only [applyCollatzKTimes_add, zero_le, tsub_zero];
      rw [ h_ind_step _ ( by linarith ), Nat.sub_succ ];
      unfold applyCollatzKTimes; simp +decide only [↓reduceIte, Nat.mul_comm, tsub_self,
        Nat.pred_eq_sub_one] ;
      unfold applyCollatz; simp +decide only [Nat.mul_mod, Nat.pow_mod, Nat.mod_self, Nat.zero_mod,
        dvd_refl, Nat.mod_mod_of_dvd, h_mult] ;
      cases h : m - ‹_› <;> simp_all +decide only [Nat.mod_succ, Nat.zero_mod, ne_eq,
        Nat.add_eq_zero_iff, and_false, not_false_eq_true, zero_pow, mul_zero, ↓reduceIte,
        Nat.pow_succ', dvd_mul_right, Nat.mul_div_assoc, mul_div_cancel_left₀,
        add_tsub_cancel_right];
      · omega;
      · unfold applyCollatzKTimes; simp +decide only [↓reduceIte] ;
    rw [ h_ind k hk_le_m, applyCollatzKTimes ] ; aesop;

/-
If the trajectory of `n` returns to `n` after `p` steps, then the trajectory is periodic
with period `p`. Specifically, the value at step `k` is the same as the value at step `k % p`.
-/
lemma applyCollatzKTimes_periodic (u : CollatzUniverse) (n p : ℕ) (h : applyCollatzKTimes u n p = n)
: ∀ k, applyCollatzKTimes u n k = applyCollatzKTimes u n (k % p) := by
  intro k
  rw [← Nat.mod_add_div k p];
  induction k / p <;> simp_all +decide [ Nat.mul_succ, ← add_assoc ];
  -- By definition of applyCollatzKTimes, we have applyCollatzKTimes u n (k % p + p) =
  -- applyCollatzKTimes u (applyCollatzKTimes u n (k % p)) p.
  have h_apply : ∀ a b : ℕ, applyCollatzKTimes u n (a + b) =
  applyCollatzKTimes u (applyCollatzKTimes u n a) b := by
    exact fun a b ↦ applyCollatzKTimes_add u n a b;
  grind +ring

/-
In a Shape Universe with multiplier `2^m`,
the trajectory of an odd number `n` is bounded by `2^m * n`.
-/
lemma shape_cycle_max (u : CollatzUniverse) (m : ℕ) (h_shape : isShapeUniverse u)
(h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : n % 2 = 1) :
∀ k, applyCollatzKTimes u n k ≤ 2^m * n := by
  intro k
  set r := k % (m + 1) with hr
  have h_r_le : applyCollatzKTimes u n r ≤ 2 ^ m * n := by
    by_cases hr0 : r = 0;
    · rw [ hr0 ];
      unfold applyCollatzKTimes; norm_num; nlinarith [ Nat.one_le_pow m 2 zero_lt_two ] ;
    · -- Since `r > 0`, let `r = s + 1`.
      -- Then `applyCollatzKTimes u n r = applyCollatzKTimes u (applyCollatz u n) s`.
      obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := Nat.exists_eq_succ_of_ne_zero hr0
      have h_r_step : applyCollatzKTimes u n r = applyCollatzKTimes u (applyCollatz u n) s := by
        rw [ hs, applyCollatzKTimes ] ; aesop;
      have h_applyCollatz : applyCollatz u n = 2 ^ m * n := by
        exact shape_odd_step u m h_shape h_mult n h_odd
      rw [h_applyCollatz] at h_r_step
      have h_cycle : applyCollatzKTimes u (2 ^ m * n) s ≤ 2 ^ m * n := by
        have h_cycle : applyCollatzKTimes u (2 ^ m * n) s = 2 ^ (m - s) * n := by
          apply shape_cycle_descent u m h_mult n h_odd s (by
          linarith [ Nat.mod_lt k ( Nat.succ_pos m ) ])
        generalize_proofs at *; (
        exact h_cycle.symm ▸ Nat.mul_le_mul_right _
          ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le _ _ ) ))
      rw [h_r_step]
      exact h_cycle
  exact (by
  rw [ applyCollatzKTimes_periodic u n ( m + 1 )
    ( shape_odd_return u m h_shape h_mult n h_odd ) ] ; exact h_r_le;)

/-
Applying Collatz `k` times to `2^a * b` (where `k <= a`) results in `2^(a-k) * b`.
This is because the number remains even and we keep dividing by 2.
-/
lemma applyCollatzKTimes_pow_two_descent (u : CollatzUniverse) (a b k : ℕ) (hk : k ≤ a) :
applyCollatzKTimes u (2^a * b) k = 2^(a-k) * b := by
  revert k b a hk;
  have h_ind : ∀ a b : ℕ, applyCollatzKTimes u (2^a * b) a = b := by
    exact fun a b ↦ applyCollatzKTimes_power_of_two_mul u b a;
  intro a b k hk_le_a
  have h_ind_step : applyCollatzKTimes u (2^a * b) k =
  applyCollatzKTimes u (2^(a-k) * (2^k * b)) k := by
    rw [ ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk_le_a ];
  convert h_ind _ _ using 1 ;
  · ring_nf;
    convert h_ind_step using 2 ;
    · ring_nf;
    ring

/-
For any number `n`, applying the Collatz function repeatedly will eventually result in an odd number
or 0. This is because if the number is even, we divide by 2, strictly decreasing it (unless it's 0).
-/
lemma eventually_odd_or_zero (u : CollatzUniverse) (n : ℕ) : ∃ k, (applyCollatzKTimes u n k) % 2 =
1 ∨ applyCollatzKTimes u n k = 0 := by
  by_contra h_no_odd_or_zero;
  -- Let's apply the definition of `applyCollatzKTimes` repeatedly.
  have h_def : ∀ k, applyCollatzKTimes u n (k + 1) = applyCollatz u (applyCollatzKTimes u n k) := by
    intro k
    rw [applyCollatzKTimes_add];
    rw [applyCollatzKTimes]
    simp only [one_ne_zero, ↓reduceIte, tsub_self];
    rw [ applyCollatzKTimes ] ;
    simp_all only [not_exists, not_or, Nat.mod_two_not_eq_one, ↓reduceIte];
  -- By definition of `applyCollatz`, if `applyCollatzKTimes u n k` is even,
  -- then `applyCollatzKTimes u n (k + 1) = applyCollatzKTimes u n k / 2`.
  have h_even_step : ∀ k, applyCollatzKTimes u n k % 2 = 0 → applyCollatzKTimes u n (k + 1) =
  applyCollatzKTimes u n k / 2 := by
    unfold applyCollatz at *;
    intro k a
    simp_all only [not_exists, not_or, Nat.mod_two_not_eq_one, ↓reduceIte];
  -- Since `applyCollatzKTimes u n k` is always even and positive, it must strictly decrease.
  have h_strict_decr : StrictAnti (fun k => applyCollatzKTimes u n k) := by
    exact strictAnti_nat_of_succ_lt (by grind);
  exact absurd ( Set.infinite_range_of_injective h_strict_decr.injective )
    ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr
      ⟨ _, Set.forall_mem_range.mpr fun k => h_strict_decr.antitone k.zero_le ⟩ )

end AristotleLemmas

theorem shapeUniversesWithPowerOfTwoMultipliersAreBounded (u : CollatzUniverse)
(h : isShapeUniverse u) (m : ∃ k : ℕ, u.multiplier = 2 ^ k) : isBounded u := by
  unfold isShapeUniverse at h
  unfold isBounded
  intro n
  obtain ⟨k, m⟩ := m
  -- unfold applyCollatzKTimes
  -- Use `eventually_odd_or_zero` to find `k` such that `n_k = applyCollatzKTimes u n k`
  -- is either odd or 0.
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, (applyCollatzKTimes u n k₀) % 2 = 1 ∨ applyCollatzKTimes u n k₀ = 0 :=
    eventually_odd_or_zero u n;
  -- Consider the set of values in the trajectory up to step
  -- `k₀`: `S = {applyCollatzKTimes u n i | i ≤ k₀}`.
  -- This set is finite, so it has a maximum `M_pre`.
  have h_finite : ∃ M_pre, ∀ i ≤ k₀, applyCollatzKTimes u n i ≤ M_pre := by
    exact ⟨ Finset.sup ( Finset.range ( k₀ + 1 ) ) fun i => applyCollatzKTimes u n i, fun i hi =>
      Finset.le_sup
        ( f := fun i => applyCollatzKTimes u n i ) ( Finset.mem_range_succ_iff.mpr hi ) ⟩;
  -- If `n_k = 0`, then the trajectory stays at 0 for all `j >= k₀`.
  by_cases h_zero : applyCollatzKTimes u n k₀ = 0;
  · -- Since `applyCollatz u 0 = 0`, the trajectory stays at 0 for all `j >= k₀`.
    have h_zero_trajectory : ∀ j ≥ k₀, applyCollatzKTimes u n j = 0 := by
      intro j hj; induction hj <;> simp_all +decide only [Nat.zero_mod, zero_ne_one, or_true,
        Nat.le_eq, Nat.succ_eq_add_one, applyCollatzKTimes_add] ;
      unfold applyCollatzKTimes; simp +decide only [↓reduceIte, applyCollatz, Nat.zero_div,
        tsub_self] ;
      unfold applyCollatzKTimes; simp +decide only [↓reduceIte] ;
    exact ⟨ Max.max h_finite.choose 0, fun j => if hj : j ≤ k₀ then
        le_trans ( h_finite.choose_spec j hj ) ( le_max_left _ _ )
      else
        le_trans ( le_of_eq ( h_zero_trajectory j ( le_of_not_ge hj ) ) ) ( le_max_right _ _ ) ⟩;
  · -- If `n_k` is odd, then let `n' = n_k`. By `shape_cycle_max`,
    -- for all `j`, `applyCollatzKTimes u n' j ≤ 2^k * n'`.
    obtain ⟨n', hn'⟩ : ∃ n', applyCollatzKTimes u n k₀ = n' ∧ n' % 2 = 1 := by
      aesop
    have h_shape_cycle : ∀ j, applyCollatzKTimes u n' j ≤ 2^k * n' := by
      apply shape_cycle_max u k h m n' hn'.right;
    -- Any step `t > k₀` can be written as `k₀ + j`.
    have h_step : ∀ t > k₀, applyCollatzKTimes u n t = applyCollatzKTimes u n' (t - k₀) := by
      intros t ht; rw [ ← hn'.1 ] ; rw [ ← Nat.add_sub_of_le ht.le ] ;
      simp +decide only [applyCollatzKTimes_add, add_tsub_cancel_left, hn'] ;
    exact ⟨ Max.max ( h_finite.choose ) ( 2 ^ k * n' ), fun t => if ht : t ≤ k₀ then
        le_trans ( h_finite.choose_spec t ht ) ( le_max_left _ _ )
      else
        le_trans ( h_step t ( not_le.mp ht ) ▸ h_shape_cycle _ ) ( le_max_right _ _ ) ⟩

-- The opposite of a bounded universe is an "unbounded" universe, where there exists a number
-- such that for all k, applying the Collatz function k times to the number results in a number
-- greater than the original number.
def isUnbounded (u : CollatzUniverse) : Prop :=
  ∃ n : ℕ, ∀ N : ℕ, ∃ k, applyCollatzKTimes u n k > N

theorem boundedEqNotUnbounded (u : CollatzUniverse) : isBounded u ↔ ¬ isUnbounded u := by
  simp [isBounded, isUnbounded]
