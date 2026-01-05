import Mathlib
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Hammer

/-!

# LoopWalk


## Main definitions

* `SimpleGraph.LoopWalk` (with accompanying pattern definitions
  `SimpleGraph.LoopWalk.nil'`, `SimpleGraph.LoopWalk.cons'`, `SimpleGraph.LoopWalk.loop`)

* `SimpleGraph.LoopWalk.map` for the induced map on walks,
  given a graph homomorphism.

## Tags
walks, moment method

-/

open Function List

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w} [DecidableEq V]
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')



/-- A LoopWalk is a sequence of adjacent vertices, allowing for consecutive visits
to the same vertex.  For vertices `u v : V`,the type `LoopWalk u v` consists of all
LoopWalks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.LoopWalk.support`.

See `SimpleGraph.LoopWalk.nil'` and `SimpleGraph.LoopWalk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive LoopWalk : V → V → Type u
  | nil {u : V} : LoopWalk u u
  | cons {u v w : V} (h : G.Adj u v) (p : LoopWalk v w) : LoopWalk u w
  | loop {u v : V} (p : LoopWalk u v): LoopWalk u v
  deriving DecidableEq

#check LoopWalk

#check LoopWalk.rec

#print LoopWalk


/-


A lot of the stuff in the next part of this file is basic tools for working with
LoopWalks, which were basically just copied from the corresponding files for Walks.
The relevant stuff to us starts at the definition of `length`.


-/


attribute [refl] LoopWalk.nil

@[simps]
instance LoopWalk.instInhabited (v : V) : Inhabited (G.LoopWalk v v) := ⟨LoopWalk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toLoopWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.LoopWalk u v :=
  LoopWalk.cons h LoopWalk.nil

namespace LoopWalk

variable {G}

/-- Pattern to get `LoopWalk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : V) : G.LoopWalk u u := LoopWalk.nil

/-- Pattern to get `LoopWalk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.LoopWalk v w) : G.LoopWalk u w := LoopWalk.cons h p

/-- Pattern to get `LoopWalk.loop` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev loop' (u v : V) (p : G.LoopWalk u v) : G.LoopWalk u v := LoopWalk.loop p

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {u v u' v'} (p : G.LoopWalk u v) (hu : u = u') (hv : v = v') :
  G.LoopWalk u' v' :=
  hu ▸ hv ▸ p

@[simp]
theorem copy_rfl_rfl {u v} (p : G.LoopWalk u v) : p.copy rfl rfl = p := rfl

@[simp]
theorem copy_copy {u v u' v' u'' v''} (p : G.LoopWalk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
theorem copy_nil {u u'} (hu : u = u') : (LoopWalk.nil : G.LoopWalk u u).copy hu hu = LoopWalk.nil := by
  subst_vars
  rfl

theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.LoopWalk v w) (hu : u = u') (hw : w = w') :
    (LoopWalk.cons h p).copy hu hw = LoopWalk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl

theorem copy_loop {u v u' v'} (p : G.LoopWalk u v) (hu : u = u') (hv : v = v') :
    (LoopWalk.loop p).copy hu hv = LoopWalk.loop (p.copy hu hv) := by
  subst_vars
  rfl

@[simp]
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.LoopWalk v' w') (hv : v' = v) (hw : w' = w) :
    LoopWalk.cons h (p.copy hv hw) = (LoopWalk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl

/-- The concatenation of two compatible walks. -/
@[trans]
def append {u v w : V} : G.LoopWalk u v → G.LoopWalk v w → G.LoopWalk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)
  | loop p, q => loop (p.append q)

/-- The reversed version of `SimpleGraph.LoopWalk.cons`, concatenating an edge to
the end of a walk. -/
def concat {u v w : V} (p : G.LoopWalk u v) (h : G.Adj v w) : G.LoopWalk u w :=
  p.append (cons h nil)

theorem concat_eq_append {u v w : V} (p : G.LoopWalk u v) (h : G.Adj v w) :
    p.concat h = p.append (cons h nil) := rfl


/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux {u v w : V} : G.LoopWalk u v → G.LoopWalk u w → G.LoopWalk v w
  | nil, q => q
  | cons h p, q => LoopWalk.reverseAux p (cons (G.symm h) q)
  | loop p, q => LoopWalk.reverseAux p (loop q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.LoopWalk u v) : G.LoopWalk v u := w.reverseAux nil


/-


This section defines the basic counting operations done on LoopWalks.


-/


/-- The length of a walk is the number of edges/darts along it. -/
@[simp, grind]
def length {u v : V} : G.LoopWalk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ
  | loop q => q.length.succ

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.LoopWalk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support
  | loop p => u::p.support


/--The `supportSet` of a LoopWalk is the set of vertices it visits.-/
def supportSet {u v : V} [DecidableEq V] (p : G.LoopWalk u v) : Finset V :=
  (support p).toFinset

/-- The `darts` of a walk is the list of steps it takes, represented as pairs of vertices. -/
@[simp, grind]
def darts {u v : V} : G.LoopWalk u v → List (V × V)
  | nil => []
  | @cons _ _ u v' _ h p => (u, v') :: p.darts
  | loop p => (u, u) :: p.darts


/--The `dartSet` of a LoopWalk is the set of edges it traverses, including loops.-/
def dartSet {u v : V} [DecidableEq V] (p : G.LoopWalk u v) : Finset (V × V) :=
  (darts p).toFinset


def connectingDarts {u v : V} : G.LoopWalk u v → List (V × V)
  | nil => []
  | @cons _ _ u v' _ h p => (u, v') :: p.connectingDarts
  | loop p => p.connectingDarts

def connectingDartsSet {u v : V} (p : G.LoopWalk u v) : Finset (V × V) :=
  (connectingDarts p).toFinset

def selfDarts {u v : V} : G.LoopWalk u v → List (V × V)
  | nil => []
  | @cons _ _ u _ _ h p => p.selfDarts
  | loop p => (u, u) :: p.selfDarts

def selfDartsSet {u v : V} (p : G.LoopWalk u v) : Finset (V × V) :=
  (selfDarts p).toFinset


/- Note on the change in darts definition: previously, the cons part of the definition was
| cons u v _ p => (u, v) :: p.darts,
where the hypothesis p was G.LoopWalk u v, and the inferred hypothesis _ was G.adj u v', for some
implicit vertex v'. Thus when I appended (u,v), it was just appending the starting and ending
endpoint of the previous LoopWalk to the list of darts.

In order to fix this, I needed to make the vertex v' explicit and then append it which you
can do with the @-pattern (which allows you to explicitly name all of the parameters). Now, the two
hypothesis are h : G.Adj u v' and p : G.LoopWalk v' v. Now we are adding (u, v') to the list of
darts.

Hovering over cons in the definition of the LoopWalk inductive type, we see
{V : Type u} {G : SimpleGraph V} {u v w : V} (h : G.Adj u v) (p : G.LoopWalk v w) as the parameters.
Thus the first two _ are the graph parameters V and G which are left implicit, u and v' are made
explicit, and the last _ left implicit for the ending vertex of the walk.
-/

/-- The edge associated to the dart. -/
def dartEdge (d : V × V) : Sym2 V :=
  Sym2.mk d

/- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.LoopWalk.darts`.-/
@[simp]
def edges {u v : V} (p : G.LoopWalk u v) : List (Sym2 V) := p.darts.map dartEdge

def connectingEdges {u v : V} (p : G.LoopWalk u v) : List (Sym2 V) :=
  p.connectingDarts.map dartEdge

def selfEdges {u v : V} (p : G.LoopWalk u v) : List (Sym2 V) :=
  p.selfDarts.map dartEdge

def edgeSet {u v: V} [DecidableEq V] (p : G.LoopWalk u v) : Finset (Sym2 V) := (edges p).toFinset

def connectingEdgeSet {u v: V} [DecidableEq V] (p : G.LoopWalk u v) : Finset (Sym2 V) :=
  (connectingEdges p).toFinset

def selfEdgeSet {u v: V} [DecidableEq V] (p : G.LoopWalk u v) : Finset (Sym2 V) :=
  (selfEdges p).toFinset

lemma dart_length_eq_walk_length {u v : V} (p : G.LoopWalk u v) : p.darts.length = p.length:= by
  induction' p with u v w h p ih
  all_goals simp [darts, length] at *
  · expose_names
    exact p_ih
  · expose_names
    exact p_ih

#check countP

/--Edge counting function.-/
def edgeCount {u v : V} (p : G.LoopWalk u v) (e : Sym2 V) : ℕ := countP (· = e) p.edges

lemma abs_w_i_eq_k {u v : V} (p : G.LoopWalk u v) : ∑(e : edgeSet p),
    edgeCount p e = p.length := by
  have h_sum_edges : ∑ e ∈ p.edgeSet, p.edgeCount e = p.length := by
    have h_edge_count : ∀ e ∈ p.edgeSet, p.edgeCount e = List.count e p.edges := by
      aesop
    have h_sum_edges : ∀ (l : List (Sym2 V)), ∑ e ∈ l.toFinset, List.count e l = l.length := by
      intros l
      apply List.sum_toFinset_count_eq_length;
    convert h_sum_edges p.edges using 1;
    have h_length_eq : ∀ (p : G.LoopWalk u v), p.length = p.edges.length := by
      intros p
      induction' p with u v w h p ih
      all_goals simp [edges] at *
      · expose_names
        rw [dart_length_eq_walk_length ih]
      · expose_names
        rw [dart_length_eq_walk_length p_1]
    apply h_length_eq;
  rw [ ← h_sum_edges, Finset.sum_coe_sort ]

/-- The loop_count of a walk is the number of loops along it. -/
def loop_count {u v : V} : G.LoopWalk u v → ℕ
  | nil => 0
  | cons _ q => q.loop_count
  | loop q => q.loop_count.succ


abbrev ClosedLoopWalk (G : SimpleGraph V) := Σ u : V, G.LoopWalk u u

/-- A walk is closed if its start and end vertices are the same. -/
@[simp]
def IsClosed {u v : V} (_ : G.LoopWalk u v) : Prop := u = v

section LoopWalkCounting

lemma vertex_edge_inequality {u v : V} (p : G.LoopWalk u v) :
  (supportSet p).card ≤ (edgeSet p).card +1 := by
  -- By induction on the length of the walk, we can show that the cardinality of the support set is at most the cardinality of the edge set plus one.
  induction' p with u v p ih;
  · -- The support set of the nil walk is {u}, and the edge set is empty.
    simp [SimpleGraph.LoopWalk.supportSet, SimpleGraph.LoopWalk.edgeSet];
    simp [SimpleGraph.LoopWalk.support, SimpleGraph.LoopWalk.edges];
  · -- By the induction hypothesis, we know that the cardinality of the support set of `p` is less than or equal to the cardinality of the edge set of `p` plus one.
    have h_ind : (SimpleGraph.LoopWalk.cons ‹_› ‹_›).supportSet.card ≤ (SimpleGraph.LoopWalk.cons ‹_› ‹_›).edgeSet.card + 1 := by
      have h_support : (SimpleGraph.LoopWalk.cons ‹_› ‹_›).supportSet = {v} ∪ (‹_› : G.LoopWalk p ih).supportSet := by
        -- The support set of the cons walk is the union of {v} and the support set of the rest of the walk.
        simp [SimpleGraph.LoopWalk.supportSet];
        ext; simp [SimpleGraph.LoopWalk.support]
      have h_edge : (SimpleGraph.LoopWalk.cons ‹_› ‹_›).edgeSet = {(Sym2.mk (v, p))} ∪ (‹_› : G.LoopWalk p ih).edgeSet := by
        simp [SimpleGraph.LoopWalk.edgeSet, SimpleGraph.LoopWalk.edges];
        rw [ SimpleGraph.LoopWalk.darts.eq_def ] ; aesop;
      -- By the induction hypothesis, we know that the cardinality of the support set of the rest of the walk is less than or equal to the cardinality of its edge set plus one.
      have h_ind : (‹_› : G.LoopWalk p ih).supportSet.card ≤ (‹_› : G.LoopWalk p ih).edgeSet.card + 1 := by
        assumption;
      by_cases hv : v ∈ (‹_› : G.LoopWalk p ih).supportSet <;> aesop;
      · -- Since $v \in p_1.supportSet$, we have $|{v} ∪ p_1.supportSet| = |p_1.supportSet|$.
        have h_card_union : ({v} ∪ p_1.supportSet).card = p_1.supportSet.card := by
          rw [ Finset.union_eq_right.mpr ( Finset.singleton_subset_iff.mpr hv ) ];
        simp [h_card_union.symm]
        exact h_card_union.symm ▸ le_trans h_ind ( add_le_add_right ( Finset.card_mono <| by aesop_cat ) _ );
      · -- Since $s(v, p)$ is a new element not in $p_1.edgeSet$, adding it to the edge set increases the cardinality by 1.
        have h_card_union : ({s(v, p)} ∪ p_1.edgeSet).card = p_1.edgeSet.card + 1 := by
          rw [ Finset.union_comm, Finset.card_union_of_disjoint ] ; aesop;
          simp +decide [ Finset.disjoint_singleton_right ];
          intro H; have := Finset.mem_union_left ( { s(v, p) } ) H;
          -- If $s(v, p)$ is in $p_1.edges$, then there must be a dart $(v, p)$ in $p_1.darts$, which would mean that $v$ is in the support of $p_1$.
          have H' : s(v, p) ∈ p_1.edges := by
            simp_all +decide [SimpleGraph.LoopWalk.edgeSet]
          have h_dart : ∃ d ∈ p_1.darts, d = (v, p) := by
            unfold SimpleGraph.LoopWalk.edges at H'; aesop;
            -- Since the edges are unordered, if (w, w_1) is in p_1.darts and its edge is s(v, p), then (w, w_1) must be either (v, p) or (p, v).
            have h_dart_cases : (w, w_1) = (v, p) ∨ (w, w_1) = (p, v) := by
              unfold SimpleGraph.LoopWalk.dartEdge at right; aesop;
            aesop;
            -- Since the support of p_1 is the list of vertices it visits, and (w, w_1) is in the darts, w_1 must be in the support.
            have h_support : w_1 ∈ p_1.support := by
              sorry
            exact False.elim <| hv <| List.mem_toFinset.mpr h_support;
          obtain ⟨ d, hd₁, rfl ⟩ := h_dart; exact hv ( by
            have h_support : ∀ {u v : V} (p : G.LoopWalk u v), ∀ d ∈ p.darts, d.1 ∈ p.support := by
              -- We can prove this by induction on the walk.
              intro u v p d hd
              induction' p with u v p ih generalizing d;
              · cases hd;
              · cases hd <;> aesop;
                · exact List.mem_cons_self;
                · exact List.mem_cons_of_mem _ ( p_ih _ _ a );
              · cases hd ; aesop;
                · exact mem_of_mem_head? rfl;
                · (expose_names; exact mem_of_mem_tail (p_ih d h_1));
            exact List.mem_toFinset.mpr ( h_support _ _ hd₁ ) ) ;
        sorry
    exact h_ind;
  · -- The support set of the loop walk is the same as the support set of the underlying walk.
    have h_support_eq : (LoopWalk.loop ‹_›).supportSet = ‹G.LoopWalk _ _›.supportSet := by
      -- The support set of the loop walk is the same as the support set of the underlying walk because adding a loop does not introduce any new vertices.
      simp [LoopWalk.supportSet];
      -- By definition of support, the starting vertex u is included in the support of the walk p.
      induction' ‹G.LoopWalk _ _› with u v p ih <;> simp [LoopWalk.support] at *;
    -- Since the support set of the loop walk is the same as the support set of the underlying walk, we can apply the induction hypothesis directly.
    rw [h_support_eq];
    refine' le_trans ‹_› _;
    unfold SimpleGraph.LoopWalk.edgeSet; aesop;
    -- Since the loop walk's edges are a superset of the underlying walk's edges, their cardinality is at least as large.
    have h_edges_superset : p.edges.toFinset ⊆ (p.loop.edges).toFinset := by
      -- Since the edges of the loop walk are the edges of the underlying walk plus the loop edge, any edge in the underlying walk's edges is also in the loop walk's edges.
      intros e he
      simp [SimpleGraph.LoopWalk.edges] at he ⊢
      aesop;
    simp [Finset.card_le_card]

end LoopWalkCounting


section CompleteGraphMultiIndexWalks

variable (n k : ℕ)
abbrev K := completeGraph (Fin n)


/-- Given a multi-index (i_0,i_1, ..., i_{k-1}), construct a LoopWalk with darts given by
(i_0, i_1), (i_1, i_2), ... , (i_{k-2}, i__{k-1}), (i_{k-1}, i_0).-/
def graphWalkMultiIndex {n k : ℕ} (hk : k > 0) (I : (Fin k) → Fin n):
    ((K n).LoopWalk (I ⟨0, hk⟩) (I ⟨0, hk⟩)) := by sorry


end CompleteGraphMultiIndexWalks

/-


Section for maps of LoopWalks


-/

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') {u v : V} : G.LoopWalk u v → G'.LoopWalk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)
  | loop p => loop (p.map f)



section CompleteGraphMaps

variable (n : ℕ)
variable (s : Equiv.Perm (Fin n))
variable {u v w x: Fin n}


def permMap (s : Equiv.Perm (Fin n)) : K n →g K n where
  toFun:= s
  map_rel':= by
    intro u v h_adj
    unfold K
    rw [top_adj] at h_adj ⊢
    rw[Function.Injective.ne_iff]
    · apply h_adj
    apply s.injective


def permMap' (s : Equiv.Perm (Fin n)) : K n ≃g K n where
  toEquiv:= s
  map_rel_iff':=by
    intros a b
    unfold K
    rw[top_adj, top_adj]
    simp

def permMapWalk (s : Equiv.Perm (Fin n)) (p : (K n).LoopWalk u v) : (K n).LoopWalk (s u) (s v):=
  p.map (K n) (permMap' n s)

@[simp]
lemma permMapWalk_nil (s : Equiv.Perm (Fin n)) (u : Fin n) :
  permMapWalk n s (LoopWalk.nil : (K n).LoopWalk u u) = LoopWalk.nil := rfl

@[simp]
lemma permMapWalk_cons (s : Equiv.Perm (Fin n))
  {u v w : Fin n} (h : (K n).Adj u v) (p : (K n).LoopWalk v w) :
  permMapWalk n s (LoopWalk.cons h p)
    = LoopWalk.cons ((permMap n s).map_adj h) (permMapWalk n s p) := rfl

@[simp]
lemma permMapWalk_loop (s : Equiv.Perm (Fin n))
  {u v : Fin n} (p : (K n).LoopWalk u v) :
  permMapWalk n s (LoopWalk.loop p) = LoopWalk.loop (permMapWalk n s p) := rfl

@[simp]
lemma permMapWalk_refl (p : (K n).LoopWalk u v) :
  permMapWalk n (Equiv.refl (Fin n)) p = p := by
  classical
  induction p with
  | nil =>
    simp
  | @cons u v w h p ih =>
    have h_adj_eq : (permMap n (Equiv.refl (Fin n))).map_adj h = h := by
      apply Subsingleton.elim
    simpa [h_adj_eq, ih]
  | @loop u v p ih =>
    simpa [ih]

@[simp]
lemma permMapWalk_comp (t s : Equiv.Perm (Fin n))
  (p : (K n).LoopWalk u v) :
  permMapWalk n t (permMapWalk n s p) = permMapWalk n (t * s) p := by
  classical
  induction p with
  | nil =>
    simp
  | @cons u v w h p ih =>
    have h_adj_eq :
        (permMap n t).map_adj ((permMap n s).map_adj h)
        = (permMap n (t * s)).map_adj h := by
      apply Subsingleton.elim
    simp [ih]
  | @loop u v p ih =>
    simp [ih]

@[simp]
lemma perm_symm_mul_self (s : Equiv.Perm (Fin n)) :
  s.symm * s = (Equiv.refl (Fin n)) := by
  ext x
  simp [Equiv.Perm.mul_def]

@[simp]
lemma perm_self_mul_symm (s : Equiv.Perm (Fin n)) :
  s * s.symm = (Equiv.refl (Fin n)) := by
  ext x
  simp [Equiv.Perm.mul_def]

def LoopWalkEquiv (p q : ClosedLoopWalk (K n)): Prop :=
  ∃ (s : Equiv.Perm (Fin n)),
    q = ⟨s p.1, permMapWalk n s p.2⟩

def LoopWalkEquiv' (p q : ClosedLoopWalk (K n)): Prop :=
  ∃ (s : Equiv.Perm (Fin n)), ∃ (h_eq : s p.1 = q.1),
    h_eq ▸ (permMapWalk n s p.2) = q.2

/-- The two definition are equal. -/
example: LoopWalkEquiv = LoopWalkEquiv' := by
 ext n w1 w2
 exact ⟨fun ⟨eq,hlw1⟩ ↦ ⟨eq, by rw [hlw1]; simp⟩,
   fun ⟨eq,hlw1',hlw2'⟩ ↦ ⟨eq,by ext <;> simp [hlw1']; rw [←hlw2']; simp⟩⟩

def LoopWalkSetoid : Setoid (ClosedLoopWalk (K n)) where
  r := LoopWalkEquiv n
  iseqv := by
    constructor
    · intro x
      classical
      rcases x with ⟨ux, px⟩
      refine ⟨Equiv.refl (Fin n), ?_⟩
      ext
      · simp
      · simp [permMapWalk_refl]
    · intro x y hxy
      classical
      rcases x with ⟨ux, px⟩
      rcases y with ⟨uy, py⟩
      rcases hxy with ⟨s, hy⟩
      refine ⟨s.symm, ?_⟩
      cases hy
      simp [permMapWalk_comp]
      have h_id : s.symm * s = Equiv.refl (Fin n) := by
        apply Equiv.Perm.ext; intro x; simp;
      have h_id : SimpleGraph.LoopWalk.permMapWalk n (Equiv.refl (Fin n)) px = px := by
        exact permMapWalk_refl n px
      grind
    · intro x y z hxy hyz
      classical
      rcases x with ⟨ux, px⟩
      rcases y with ⟨uy, py⟩
      rcases z with ⟨uz, pz⟩
      rcases hxy with ⟨s1, hy⟩
      rcases hyz with ⟨s2, hz⟩
      refine ⟨s2 * s1, ?_⟩
      cases hy
      cases hz
      ext
      · simp [Equiv.Perm.mul_def]
      · simp [permMapWalk_comp]


lemma walk_vertex_card_equiv {n : ℕ} (p q : ClosedLoopWalk (K n)) (heq : LoopWalkEquiv n p q) :
  (supportSet p.2).card = (supportSet q.2).card := by
    obtain ⟨ s, hs ⟩ := heq;
    rw [hs];
    -- Since these two sets are equal, their cardinalities are equal.
    have h_card_eq : (p.snd.supportSet).image s = (SimpleGraph.LoopWalk.permMapWalk n s p.snd).supportSet := by
      -- By definition of `permMapWalk`, the support of the permuted walk is the image of the support of the original walk under `s`.
      have h_support_eq : (SimpleGraph.LoopWalk.permMapWalk n s p.snd).support = List.map (⇑s) p.snd.support := by
        have h_support_eq : ∀ (u v : Fin n) (p : (K n).LoopWalk u v), (SimpleGraph.LoopWalk.permMapWalk n s p).support = List.map (⇑s) p.support := by
          intros u v p
          induction' p with u v w h p ih
          · rfl;
          · -- By definition of `permMapWalk`, the support of the permuted walk is the image of the support of the original walk under `s`. We can prove this by induction on the walk. For the cons case, we have:
            have h_support_eq_cons : (SimpleGraph.LoopWalk.permMapWalk n s (SimpleGraph.LoopWalk.cons p ih)).support = s v :: (SimpleGraph.LoopWalk.permMapWalk n s ih).support := by
              exact?
            (generalize_proofs at *; aesop;);
          · -- By definition of `support`, the support of a loop walk is the same as the support of the underlying walk.
            have h_support_loop : ∀ (u v : Fin n) (p : (K n).LoopWalk u v), (SimpleGraph.LoopWalk.loop p).support = u :: p.support := by
              aesop
            aesop
        exact h_support_eq _ _ _
      unfold SimpleGraph.LoopWalk.supportSet; aesop;
    rw [ ← h_card_eq, Finset.card_image_of_injective _ s.injective ]

lemma walk_edge_card_equiv {n : ℕ} (p q : ClosedLoopWalk (K n)) (heq : LoopWalkEquiv n p q) :
  (edgeSet p.2).card = (edgeSet q.2).card := by sorry



end CompleteGraphMaps


/-


Lemmas relating LoopWalks to matrices


-/


/-- The product of matrix entries along a loop walk's darts. -/
def dartProduct {n : ℕ} {α : Type*} [Semiring α] (X : Matrix (Fin n) (Fin n) α)
    {u : Fin n} (w : LoopWalk (completeGraph (Fin n)) u u) : α :=
  w.darts.foldr (fun d acc => X d.1 d.2 * acc) 1


/-- There are finitely many LoopWalks of a given length k on a finite graph. -/
instance fintypeWalksOfFiniteLength {n : ℕ } {G : SimpleGraph (Fin n)} {u : Fin n}
[DecidableRel G.Adj] (k : ℕ) : Fintype {w : G.LoopWalk u u // w.length = k} := by
  induction k with
  | zero => sorry
  | succ k ih =>
  sorry


/-- The sum of dart products over all closed walks of length k on the complete graph on n vertices.
This sum is finite because there are finitely many such walks of a given length. -/
def sumClosedWalkProducts {α : Type*} [Ring α] (n k : ℕ)
    (X : Matrix (Fin n) (Fin n) α) : α :=
  ∑ u : Fin n, ∑ (w : {w : LoopWalk (completeGraph (Fin n)) u u // w.length = k}),
    dartProduct X w.val

/-- For a natural number k ≥ 1 and an n × n matrix X, the trace of X^k equals the sum over
all closed loop walks of length k on the complete graph of n vertices, where each walk
contributes the product of matrix entries corresponding to its darts. -/
theorem trace_pow_eq_sum_over_walks {n k : ℕ} {α : Type*} [Ring α]
    (hk : k ≥ 1) (X : Matrix (Fin n) (Fin n) α) :
  Matrix.trace (X ^ k) = sumClosedWalkProducts n k X := by
  sorry



/-


Section for testing definitions:


-/




/- Below is an example of how these definitions can be used on the complete graph.
You can (and should, to make sure I didn't mess up the definition) play around
with them to see how they work for different walks on the complete graph. -/


/-
First, import the complete graph on 6 vertices. Then construct a simple loopwalk
of length 2 on the complete graph on 6 vertices that starts at vertex 1,
goes to vertex 3, and then ends at vertex 2.
-/

def G_comp := completeGraph (Fin 6)

#print G_comp

/-Auxiliary lemma we will use that says any two distinct vertices on the complete graph
are adjacent-/
@[simp]
lemma completeGraph_adj (m : Fin 6) (n : Fin 6) (hmn : m ≠ n) : G_comp.Adj m n := by
  rw[G_comp]
  rw[completeGraph]
  rw[top_adj]
  exact hmn

def myWalk : G_comp.LoopWalk 1 2 :=
  LoopWalk.cons
    (completeGraph_adj 1 3 (by decide))
    (LoopWalk.cons (completeGraph_adj 3 2 (by decide)) LoopWalk.nil)

#check IsClosed myWalk


/- The walk above, but reversed -/
def myWalkReverse : G_comp.LoopWalk 2 1 :=
  LoopWalk.cons
    (completeGraph_adj 2 3 (by decide))
    (LoopWalk.cons (completeGraph_adj 3 1 (by decide)) LoopWalk.nil)

/-Reversing the walk is the same is the function `reverse` defined above-/
lemma reverse_eq : myWalkReverse = reverse myWalk := by
  rfl

/- A LoopWalk that starts at vertex 1 and does one loop at vertex 1-/
def oneLoopWalk : G_comp.LoopWalk 1 1 :=
  LoopWalk.loop LoopWalk.nil

/-  In the above LoopWalk Lean infers that the loop should be at vertex 1, however we can
define it for arbitrary vertices as below  -/
def arbitraryLoopWalk (m : Fin 6): G_comp.LoopWalk m m :=
  LoopWalk.loop LoopWalk.nil

/- A more complicated LoopWalk: 1 → 4 → 1 → 1 → 3 → 5 (loop at the repeated 1's)-/
def complicatedWalk : G_comp.LoopWalk 1 5 :=
  LoopWalk.cons
  ((completeGraph_adj 1 4 (by decide)))
  (LoopWalk.cons
  ((completeGraph_adj 4 1 (by decide)))
  (LoopWalk.loop
  (LoopWalk.cons
    (completeGraph_adj 1 3 (by decide))
    (LoopWalk.cons (completeGraph_adj 3 5 (by decide)) LoopWalk.nil))))

#eval selfDarts complicatedWalk
#eval connectingDarts complicatedWalk
#eval edgeCount complicatedWalk (Sym2.mk (1,4))
#eval edgeCount complicatedWalk (Sym2.mk (1,1))
#eval length complicatedWalk
#eval loop_count complicatedWalk
#eval support complicatedWalk
#eval darts complicatedWalk


def moreComplicatedWalk : G_comp.LoopWalk 1 5 :=
  LoopWalk.cons
  ((completeGraph_adj 1 4 (by decide)))
  (LoopWalk.cons
  ((completeGraph_adj 4 1 (by decide)))
  (LoopWalk.loop
  (LoopWalk.loop
  (LoopWalk.cons
    (completeGraph_adj 1 3 (by decide))
    (LoopWalk.cons (completeGraph_adj 3 5 (by decide)) LoopWalk.nil)))))

#eval loop_count moreComplicatedWalk
#eval darts moreComplicatedWalk
#eval edges moreComplicatedWalk

/- A closed complicated LoopWalk: 1 → 4 → 1 → 1 → 3 → 1 (loop at the repeated 1's)-/
def closedComplicatedWalk : G_comp.LoopWalk 0 0 :=
  LoopWalk.cons
  ((completeGraph_adj 0 4 (by decide)))
  (LoopWalk.cons
  ((completeGraph_adj 4 1 (by decide)))
  (LoopWalk.loop
  (LoopWalk.cons
    (completeGraph_adj 1 3 (by decide))
    (LoopWalk.cons (completeGraph_adj 3 0 (by decide)) LoopWalk.nil))))

#eval length myWalk
#eval loop_count myWalk
#eval support myWalk
#eval darts myWalk
#eval edges myWalk


#eval support myWalkReverse
#eval support (reverse myWalk)

#eval support oneLoopWalk
#eval darts oneLoopWalk
#eval support (reverse complicatedWalk)


def subtract_one : (Fin 6) → (Fin 6) :=
  fun x ↦ (x - 1)

#eval subtract_one 3
#eval subtract_one 0 --Lean treats Fin 6 as Z/6 where 0 is identified with 6

/-
The function `subtract_one` induces a graph homomorphism on the complete graph
because it is an injective function. Fill in each `sorry` for practice.
-/

lemma subtract_one_injective : Injective subtract_one := by
  sorry


def subtract_one_hom : G_comp →g G_comp where
  toFun := subtract_one
  map_rel' := by
    sorry

#check LoopWalk.map


#eval support myWalk
#eval! support ((LoopWalk.map G_comp subtract_one_hom) myWalk)
#eval! length ((LoopWalk.map G_comp subtract_one_hom) myWalk)


/-I'm using ℚ as the type of the entries here so that I can check things with #eval. ℚ and ℕ are
computable, but if I used ℝ things would be messy (see #eval myMatrix_3), as the reals are
defined as equivalence classes of Cauchy sequences of rationals. -/
def myMatrix_1 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 2; 3, 4]

def myMatrix_2 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2, 5; 3, 1]

def myMatrix_3 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 2; 3, 4]

#check myMatrix_1
#eval myMatrix_1 + myMatrix_2

#check myMatrix_3
#eval myMatrix_3

/-Define a 6 by 6 matrix-/
def testMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
 !![1, 2, 3, 4, 5, 6;
 8, 7, 2, 9, 0, 1;
 -1, 4, 3, 10, 3, 1;
 4, 0, 0, 1, 2, 3;
 9, 8, 7, 6, 4, 3;
 1, 2, 3, 4, 5, 6]

#eval dartProduct testMatrix oneLoopWalk

#eval darts closedComplicatedWalk

/-Matrix indexing starts from 0 here. Takes the product of the
(0, 4), (4, 1), (1, 1), (1, 3), and (3, 0) entries of testMatrix. These are 5, 8, 7, 9, 4. The
product is 10080.
 -/
#eval dartProduct testMatrix closedComplicatedWalk


/-The folllowing eval should give the pro-/
--#eval sumClosedWalkProducts 6 2 testMatrix


/-
Results we will need:

The notion of `support`, `darts`, and `edges` (these are ordered Lists)

The unordered versions of `support`, `darts`, and `edges` (send the lists above to multisets)

A count of the number of distinct elements of `support` (|G| in the blueprint)

A count of the number of distinct elements of `edges`

A count of the number of `loop`s in a walk
  -- to help define the refined sets of walks

The map w that takes a list of edges and returns the traversal counts of each edge
  -- This will let us define the truncated set `w ≥ 2` where each edge is traversed twice

Notion of walk isomorphims/equivalance
  -- This will be induced by a graph isomorphism
  -- For us this will be an isomorphism f : Cₙ → Cₙ, where Cₙ is the complete graph on n vertices
  -- Two walks u and v are said to be isomorphic if there exists a graph isomormphism f such that
      map f u = v

-/

end LoopWalk

end SimpleGraph
