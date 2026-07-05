import BEDC.Derived.FiniteRefutationBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteRefutationBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteRefutationBoundaryNamecertObligations [AskSetup] [PackageSetup]
    {A R D E H C P N botR : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory N →
      PkgSig bundle P pkg →
        SemanticNameCert
            (fun row : BHist => hsame row N ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row botR)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
            hsame ∧
          finiteRefutationBoundaryFields
              (FiniteRefutationBoundaryUp.mk A R D E H C P N botR) =
            [A, R, D, E, H, C, P, N, botR] ∧
            finiteRefutationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Pkg ProbeBundle SemanticNameCert hsame
  intro nUnary pkgRow
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row botR)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgRow⟩
  }
  exact ⟨cert, rfl, rfl⟩

theorem FiniteRefutationBoundary_ground_loop_soundness
    {A R D E H C P N botR replay transportedRoute : BHist}
    (packet : FiniteRefutationBoundaryUp)
    (hpacket : packet = FiniteRefutationBoundaryUp.mk A R D E H C P N botR)
    (refutationReplay : Cont A R replay)
    (transportReplay : Cont replay H transportedRoute)
    (terminalReadback : hsame transportedRoute botR) :
    hsame botR (append (append A R) H) ∧
      List.Mem botR (finiteRefutationBoundaryFields packet) ∧
      hsame N N ∧ hsame P P := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases hpacket
  cases refutationReplay
  cases transportReplay
  cases terminalReadback
  exact
    ⟨rfl,
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.head _)))))))),
      hsame_refl N, hsame_refl P⟩

theorem FiniteRefutationBoundary_vision_concretization [AskSetup] [PackageSetup]
    {A R D E H C P N botR replay transportedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : FiniteRefutationBoundaryUp) :
    packet = FiniteRefutationBoundaryUp.mk A R D E H C P N botR →
      UnaryHistory N →
        PkgSig bundle P pkg →
          Cont A R replay →
            Cont replay H transportedRoute →
              hsame transportedRoute botR →
                SemanticNameCert
                    (fun row : BHist => hsame row N ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row botR)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                    hsame ∧
                  List.Mem botR (finiteRefutationBoundaryFields packet) ∧
                    hsame botR (append (append A R) H) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg SemanticNameCert hsame
  intro hpacket nUnary pkgRow refutationReplay transportReplay terminalReadback
  have obligations :=
    FiniteRefutationBoundaryNamecertObligations
      (A := A) (R := R) (D := D) (E := E) (H := H) (C := C) (P := P) (N := N)
      (botR := botR) (bundle := bundle) (pkg := pkg) nUnary pkgRow
  have groundLoop :=
    FiniteRefutationBoundary_ground_loop_soundness
      (A := A) (R := R) (D := D) (E := E) (H := H) (C := C) (P := P) (N := N)
      (botR := botR) packet hpacket refutationReplay transportReplay terminalReadback
  exact ⟨obligations.left, groundLoop.right.left, groundLoop.left⟩

theorem FiniteRefutationBoundary_decision_row_scope [AskSetup] [PackageSetup]
    {decision witness audit boundary replay provenance localName readback packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory decision ->
      UnaryHistory witness ->
        UnaryHistory audit ->
          UnaryHistory boundary ->
            UnaryHistory replay ->
              UnaryHistory provenance ->
                UnaryHistory localName ->
                  Cont decision witness readback ->
                    Cont provenance localName packageRead ->
                      PkgSig bundle packageRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row decision ∨ hsame row witness ∨ hsame row audit ∨
                                hsame row boundary ∨ hsame row readback ∨ hsame row packageRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont decision witness readback ∧
                                PkgSig bundle packageRead pkg)
                            hsame ∧
                          UnaryHistory readback ∧ UnaryHistory packageRead := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro decisionUnary witnessUnary _auditUnary _boundaryUnary _replayUnary provenanceUnary
    localNameUnary decisionRead packageRoute packageSig
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed decisionUnary witnessUnary decisionRead
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed provenanceUnary localNameUnary packageRoute
  have sourceReadback :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row decision ∨ hsame row witness ∨ hsame row audit ∨
              hsame row boundary ∨ hsame row readback ∨ hsame row packageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont decision witness readback ∧ PkgSig bundle packageRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceReadback
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, decisionRead, packageSig⟩
  }
  exact ⟨cert, readbackUnary, packageReadUnary⟩

end BEDC.Derived.FiniteRefutationBoundaryUp
