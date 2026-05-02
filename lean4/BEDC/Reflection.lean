/-
BEDC.Reflection: statement-only scaffolds for the capstone chapter
`papers/bedc/parts/capstones/reflection_and_limits.tex`. Each definition
records the proposition asserted by a chapter theorem; later R-rounds
substantiate the body with the actual Lean statement and then add a
matching theorem proof, at which point the paper marker switches from
\leanstmt to \leanchecked.
-/

namespace BEDC.Reflection

/-- Irreducibility of the form of distinction (statement scaffold). -/
def form_of_distinction_irreducible : Prop := True
-- TODO: refine to the assertion that every classifier on every BEDC
-- carrier presupposes the inductive constructor declaration of `Mark`;
-- equivalently, no `def`-level primitive supplies the form of distinction.

/-- Definition-classifier correspondence (statement scaffold). -/
def definition_classifier_correspondence : Prop := True
-- TODO: refine to the full statement once a Lean encoding of "definition over
-- a generator base" exists; the body will assert the natural isomorphism
-- between such definitions and naming-certificate classifiers.

/-- Inductive types as classifier closures (statement scaffold). -/
def inductive_as_classifier_closure : Prop := True
-- TODO: refine to the Lambek-style initial F-algebra characterisation
-- formulated inside BEDC; the body will quantify over a constructor
-- signature and assert isomorphism with the generator-closure classifier.

/-- Internal description of the calculus of inductive constructions
(statement scaffold). -/
def internal_cic_interpretation : Prop := True
-- TODO: refine to the existence of an internal CIC-shaped structure
-- assembled from W-type-shaped naming certificates with stratified
-- universe classifiers.

/-- BEDC self-description (statement scaffold). -/
def bedc_self_description : Prop := True
-- TODO: refine to the universal translation from formal CIC claims about
-- inductive types to internal claims expressible inside BEDC over the
-- structure asserted by `internal_cic_interpretation`.

/-- Closed ground loop and open meta loop (statement scaffold). -/
def two_loops_theorem : Prop := True
-- TODO: refine to the conjunction asserting (a) the form of distinction
-- closes at one layer, and (b) the reflection map onto the host kernel
-- remains open by Tarski undefinability and the runtime/object boundary.

/-- Continuation as Plotkin-style small-step relation (statement scaffold). -/
def computation_as_continuation_correspondence : Prop := True
-- TODO: refine to the natural isomorphism between Cont and the small-step
-- transition relation of an arbitrary closed program syntax, with
-- well-foundedness corresponding to termination and hsame to behavioural
-- equivalence.

/-- Type checking as Ext membership (statement scaffold). -/
def type_checking_as_ext_membership : Prop := True
-- TODO: refine to the assertion that for every typed term language, the
-- well-typedness predicate coincides with Ext in a corresponding naming
-- certificate, and that subject reduction is the certificate's classifier
-- closure.

/-- Compiler as naming-certificate morphism (statement scaffold). -/
def compilation_as_namecert_morphism : Prop := True
-- TODO: refine to the bijection between hsame-preserving compilers and
-- naming-certificate morphisms, with compiler correctness identified as
-- the morphism property in the category of naming certificates.

/-- Halting problem as Tarski-style fixed-point obstruction over Cont
(statement scaffold). -/
def halting_as_form_of_distinction_fixed_point : Prop := True
-- TODO: refine to a Tarski-style argument inside BEDC: assuming a halting
-- classifier produces a self-referential naming certificate whose
-- extension contradicts itself. The obstruction is the form of distinction
-- read at the meta level.

end BEDC.Reflection
