import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Batteries.Data.Rat.Basic
import Mathlib.Algebra.Ring.Defs
import Hammer


/-!

# LoopWalk


## Main definitions

* `SimpleGraph.LoopWalk` (with accompanying pattern definitions
  `SimpleGraph.LoopWalk.nil'`, `SimpleGraph.LoopWalk.cons'`, `SimpleGraph.LoopWalk.loop`)

* `SimpleGraph.LoopWalk.map` for the induced map on walks,
  given an (injective) graph homomorphism.

## Tags
walks, moment method

-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

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

/- A lot of the stuff in the next part of this file is basic tools for working with
LoopWalks, which were basically just copied from the corresponding files for Walks.
The relevant stuff to us starts at the definition of `length`. -/

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
protected def copy {u v u' v'} (p : G.LoopWalk u v) (hu : u = u') (hv : v = v') : G.LoopWalk u' v' :=
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


/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.LoopWalk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ
  | loop q => q.length.succ


--   /-- There are finitely many walks of a given length on a finite graph. -/
-- instance fintypeWalksOfLength {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] (k : ℕ) :
--     Fintype {p : G.ClosedLoopWalk // p.2.length = k} := by
--   -- This is provable by induction on k, but is non-trivial.
--   -- For now, we can mark it as an axiom to proceed.
--   -- A full proof would likely involve constructing the set of walks recursively.
--   classical
--   apply Fintype.ofEquiv (Σ (u : V), {p : G.LoopWalk u u // p.length = k})
--   exact Equiv.sigmaCongrRight fun u => Equiv.subtypeEquivRight (fun p => by simp)



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


/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.LoopWalk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support
  | loop p => u::p.support


/-- The `darts` of a walk is the list of steps it takes, represented as pairs of vertices. -/
def darts {u v : V} : G.LoopWalk u v → List (V × V)
  | nil => []
  | @cons _ _ u v' _ h p => (u, v') :: p.darts
  | loop p => (u, u) :: p.darts

/- Note on the change in darts definition: previously, the cons part of the definition was
| cons u v _ p => (u, v) :: p.darts,
where the hypothesis p was G.LoopWalk u v, and the inferred hypothesis _ was G.adj u v', for some
implicit vertex v'. Thus when I appended (u,v), it was just appending the starting and ending
endpoint of the previous LoopWalk to the list of darts.

In order to fix this, I needed to make the vertex v' explicit and then append it, which you
can do with the @-pattern which allows you to explicitly name all of the parameters. Now, the two
hypothesis are h : G.Adj u v' and p : G.LoopWalk v' v. Now we are adding (u, v') to the list of
darts.

Hovering over cons in the definition of the LoopWalk inductive type, we see
{V : Type u} {G : SimpleGraph V} {u v w : V} (h : G.Adj u v) (p : G.LoopWalk v w) as the parameters.
Thus the first two _ are the graph parameters V and G which are left implicit, u and v' are made
explicit, and the last _ left implicit for the ending vertex of the walk.
-/

#check Dart
/- We may need to change how Darts are defined, since it might require that the two vertices
are adjacent, which isn't true for a vertex and itself. The definition above seems to work,
but we should double check it at some point.-/


/-- The edge associated to the dart. -/
def dartEdge (d : V × V) : Sym2 V :=
  Sym2.mk d

/- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.LoopWalk.darts`.-/
def edges {u v : V} (p : G.LoopWalk u v) : List (Sym2 V) := p.darts.map dartEdge


/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') {u v : V} : G.LoopWalk u v → G'.LoopWalk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)
  | loop p => loop (p.map f)


/-- The loop_count of a walk is the number of loops along it. -/
def loop_count {u v : V} : G.LoopWalk u v → ℕ
  | nil => 0
  | cons _ q => q.loop_count
  | loop q => q.loop_count.succ


abbrev ClosedLoopWalk (G : SimpleGraph V) := Σ u : V, G.LoopWalk u u

/-- A walk is closed if its start and end vertices are the same. -/
@[simp]
def IsClosed {u v : V} (_ : G.LoopWalk u v) : Prop := u = v

#print ClosedLoopWalk




/-
Lemma: For k ∈ ℕ, k ≥ 2, and X an n × n matrix, we have
Trace(X^k) = ∑_{Loopwalks w on the complete graph on n vertices satisfying IsClosed w,
and length w = k } X_{i_1 i_2}...X_{i_k i_1},
where (i_1, i_2), (i_2, i_3), ... (i_k, i_1) are the darts of the loopwalk.
In other words, the trace of the kth power of a matrix can be written as a sum over closed LoopWalks
on the complete graph on n vertices with length equal to k.
-/


/-- The product of matrix entries along a loop walk's darts. -/
def dartProduct {n : ℕ} {α : Type*} [Semiring α] (X : Matrix (Fin n) (Fin n) α)
    {u : Fin n} (w : LoopWalk (completeGraph (Fin n)) u u) : α :=
  w.darts.foldr (fun d acc => X d.1 d.2 * acc) 1


/-- There are finitely many walks of a given length on a finite graph. -/
instance fintypeWalksOfLength {n : ℕ } {G : SimpleGraph (Fin n)} {u : Fin n} [DecidableRel G.Adj]
(k : ℕ) : Fintype {w : G.LoopWalk u u // w.length = k} := by
  apply?
  sorry


/-- The sum of dart products over all closed walks of length k on the complete graph of n vertices.
This sum is finite because there are finitely many such walks of a given length. -/
def sumClosedWalkProducts {α : Type*} [Semiring α] (n k : ℕ)
    (X : Matrix (Fin n) (Fin n) α) : α :=
  ∑ u : Fin n, ∑ (w : {w : LoopWalk (completeGraph (Fin n)) u u // w.length = k}),
    dartProduct X w.val

/-- For a natural number k ≥ 2 and an n × n matrix X, the trace of X^k equals the sum over
all closed loop walks of length k on the complete graph of n vertices, where each walk
contributes the product of matrix entries corresponding to its darts. -/
theorem trace_pow_eq_sum_over_walks {n k : ℕ} {α : Type*} [Semiring α]
    (hk : k ≥ 2) (X : Matrix (Fin n) (Fin n) α) :
  Matrix.trace (X ^ k) = sumClosedWalkProducts n k X := by
  sorry

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
