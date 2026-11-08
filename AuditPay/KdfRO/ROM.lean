/-
Copyright (c) 2026 Elkana Tovey, Yossi Gilad, Aviv Zohar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AuditPay.Prob
import VCVio.OracleComp.QueryTracking.RandomOracle.Programming
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.ProbabilityBounds

/-!
# The key-derivation function as a random oracle: running games

In the games of `AuditPay.KdfRO` the key-derivation function is a random oracle with domain `X`
(the Diffie–Hellman point, or a pair of points) and range `Key`. A game is an oracle computation
`OracleComp (unifSpec + (X →ₒ Key)) α`: it may sample uniformly and **query** the KDF, and both
the challenger and the adversary are parts of this computation. The adversary's parts are
arbitrary oracle computations, so the adversary has oracle access to the KDF and nothing else:
it cannot inspect the oracle's table.

A game is *run in the random oracle model* with VCV-io's handler `OracleSpec.romImpl`: uniform
queries are forwarded, and a KDF query is answered by lazy sampling (a fresh uniform key on the
first query at a point, the cached key afterwards). `roRun oa c` is that run from the cache `c`,
returning the output together with the final cache. From the empty cache this is the standard
random oracle: by VCV-io's `OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable` it has
the same output distribution as sampling a uniformly random function `X → Key` up front and
answering every query from it.

The final cache holds exactly the points that were queried. This file collects:

* the equations for running a game step by step (`roRun_bind`, `roRun_liftM`, `roRun_query`);
* `prEvent_fresh_le_query`, the programming step: replacing the answer to one KDF query by a
  fresh key is invisible unless that point is queried at some other time;
* `cachedPoints`, the list of points a cache holds, and its length under a query bound
  (`length_cachedPoints_le`).
-/

open OracleComp OracleSpec ENNReal

namespace AuditPay.KdfRO

variable {X Key α β : Type} [DecidableEq X] [SampleableType Key]

/-- The predicate selecting the KDF queries of a game (as opposed to its uniform-sampling
queries). `IsQueryBoundP oa IsKdfQuery q` says that `oa` makes at most `q` KDF queries on every
execution path. -/
abbrev IsKdfQuery (t : ℕ ⊕ X) : Prop := t.isRight = true

/-- Run a game in the random oracle model from the cache `c`: uniform queries are sampled, KDF
queries are answered by lazy sampling. Returns the output and the final cache. -/
noncomputable def roRun (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    (c : (X →ₒ Key).QueryCache) : ProbComp (α × (X →ₒ Key).QueryCache) :=
  (simulateQ (X →ₒ Key).romImpl oa).run c

/-- The experiment defined by a game: its output when run in the random oracle model from the
empty cache (VCV-io's `ProbCompRuntime.rom`). -/
noncomputable def roExec (oa : OracleComp (unifSpec + (X →ₒ Key)) α) : ProbComp α :=
  (simulateQ (X →ₒ Key).romImpl oa).run' ∅

theorem roExec_eq (oa : OracleComp (unifSpec + (X →ₒ Key)) α) :
    roExec oa = Prod.fst <$> roRun oa ∅ := rfl

/-! ## Running a game step by step -/

@[simp]
theorem roRun_pure (a : α) (c : (X →ₒ Key).QueryCache) :
    roRun (pure a : OracleComp (unifSpec + (X →ₒ Key)) α) c = pure (a, c) := by
  simp [roRun]

@[simp]
theorem roRun_bind (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    (ob : α → OracleComp (unifSpec + (X →ₒ Key)) β) (c : (X →ₒ Key).QueryCache) :
    roRun (oa >>= ob) c = roRun oa c >>= fun z => roRun (ob z.1) z.2 := by
  simp only [roRun, simulateQ_bind, StateT.run_bind]

@[simp]
theorem roRun_map (f : α → β) (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    (c : (X →ₒ Key).QueryCache) :
    roRun (f <$> oa) c = (fun z => (f z.1, z.2)) <$> roRun oa c := by
  simp only [roRun, simulateQ_map, StateT.run_map]

/-- A step that does not use the KDF samples and leaves the cache unchanged. -/
@[simp]
theorem roRun_liftM (pc : ProbComp α) (c : (X →ₒ Key).QueryCache) :
    roRun (liftM pc : OracleComp (unifSpec + (X →ₒ Key)) α) c = (·, c) <$> pc := by
  simp only [roRun, OracleSpec.simulateQ_romImpl_liftM_run]

@[simp]
theorem roRun_ite (p : Prop) [Decidable p] (oa ob : OracleComp (unifSpec + (X →ₒ Key)) α)
    (c : (X →ₒ Key).QueryCache) :
    roRun (if p then oa else ob) c = if p then roRun oa c else roRun ob c := by
  split_ifs <;> rfl

/-- A KDF query returns the cached key if there is one, and otherwise samples and caches a fresh
uniform key. -/
theorem roRun_query (Z : X) (c : (X →ₒ Key).QueryCache) :
    roRun (query (spec := X →ₒ Key) Z : OracleComp (unifSpec + (X →ₒ Key)) Key) c =
      match c Z with
      | some u => pure (u, c)
      | none => ($ᵗ Key) >>= fun u => pure (u, c.cacheQuery Z u) := by
  rw [roRun, roSim.simulateQ_HasQuery_query, randomOracle.run_eq]
  cases c Z <;> rfl

/-- A run only extends the cache: cached keys are never changed or forgotten. -/
theorem le_of_mem_support_roRun (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    {c : (X →ₒ Key).QueryCache} {z : α × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun oa c)) : c ≤ z.2 :=
  OracleComp.le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl oa hz

/-- A point cached before a run is still cached after it. -/
theorem isSome_of_mem_support_roRun (oa : OracleComp (unifSpec + (X →ₒ Key)) α)
    {c : (X →ₒ Key).QueryCache} {z : α × (X →ₒ Key).QueryCache}
    (hz : z ∈ support (roRun oa c)) {Z : X} (hZ : (c Z).isSome) : (z.2 Z).isSome :=
  QueryCache.isSome_mono (le_of_mem_support_roRun oa hz) hZ

/-! ## The programming step -/

/-- **Replacing one KDF answer by a fresh key.** Compare a game that obtains a key by querying the
KDF at `Z` and then continues with `post`, with the game that samples a fresh key instead. An
event of the second game in which `Z` is never queried (it is uncached at the end) is at most as
likely as the same event in the first game. -/
theorem prEvent_fresh_le_query (Z : X) (post : Key → OracleComp (unifSpec + (X →ₒ Key)) β)
    (E : β → Prop) (c : (X →ₒ Key).QueryCache) :
    Pr{let z ← ($ᵗ Key) >>= fun key => roRun (post key) c}[E z.1 ∧ z.2 Z = none] ≤
      Pr{let z ← roRun (query (spec := X →ₒ Key) Z) c >>= fun w => roRun (post w.1) w.2}[
        E z.1] := by
  rw [roRun_query]
  cases hc : c Z with
  | some v =>
    refine le_of_eq_of_le ?_ zero_le
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => ?_
    obtain ⟨key, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    have := isSome_of_mem_support_roRun (post key) hz (Z := Z) (by rw [hc]; rfl)
    rw [hz'.2] at this
    exact Bool.false_ne_true this
  | none =>
    simp only [bind_assoc, pure_bind]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun key => ?_
    exact roSim.prEvent_run_uncached_le_run_cacheQuery (post key) Z key E c hc

/-! ## The points of a cache, and query bounds -/

/-- A run of a game that makes at most `q` KDF queries adds at most `q` entries to the cache. -/
theorem toSet_encard_le_of_mem_support_roRun {oa : OracleComp (unifSpec + (X →ₒ Key)) α} {q : ℕ}
    (h : IsQueryBoundP oa IsKdfQuery q) {c : (X →ₒ Key).QueryCache}
    {z : α × (X →ₒ Key).QueryCache} (hz : z ∈ support (roRun oa c)) :
    z.2.toSet.encard ≤ c.toSet.encard + q := by
  refine h.resource_le_add_of_mem_support_run_simulateQ (fun c => c.toSet.encard)
    (fun t c w hw => ?_) hz
  rcases t with i | t
  · obtain ⟨samp, hsamp⟩ :=
      OracleComp.exists_run_unifFwdImpl_add_randomOracle_inl (spec := X →ₒ Key) i c
    rw [hsamp, support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    simp
  · rw [OracleSpec.romImpl_apply_inr] at hw
    rcases hc : c t with _ | u
    · rw [QueryImpl.withCaching_run_none _ hc, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      simpa [IsKdfQuery] using QueryCache.toSet_encard_cacheQuery_le c t u
    · rw [QueryImpl.withCaching_run_some _ hc] at hw
      simp_all

/-- The points at which a cache holds a key, as a list without repetitions. After a run from the
empty cache these are the points at which the KDF was queried. (The list is obtained by
enumerating the finite domain `X`; a concrete reduction would keep a log of the queries.) -/
noncomputable def cachedPoints [Finite X] (c : (X →ₒ Key).QueryCache) : List X :=
  (Set.toFinite {Z | (c Z).isSome}).toFinset.toList

omit [DecidableEq X] [SampleableType Key] in
@[simp]
theorem mem_cachedPoints [Finite X] {c : (X →ₒ Key).QueryCache} {Z : X} :
    Z ∈ cachedPoints c ↔ (c Z).isSome := by
  simp [cachedPoints]

omit [DecidableEq X] [SampleableType Key] in
/-- A cache has at most as many points as entries. -/
theorem length_cachedPoints_le [Finite X] (c : (X →ₒ Key).QueryCache) :
    ((cachedPoints c).length : ℕ∞) ≤ c.toSet.encard := by
  rw [cachedPoints, Finset.length_toList, ← Set.Finite.encard_eq_coe_toFinset_card]
  exact QueryCache.encard_le_toSet_encard _ fun _ h => h

end AuditPay.KdfRO
