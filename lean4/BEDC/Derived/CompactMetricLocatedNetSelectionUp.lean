import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactMetricLocatedNetSelectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive CompactMetricLocatedNetSelectionUp : Type where
  | mk
      (compactSource dyadicTolerance streamWindow regularReadback realSeal transport replay
        provenance nameCert : BHist) :
      CompactMetricLocatedNetSelectionUp
  deriving DecidableEq

def compactMetricLocatedNetSelectionFields :
    CompactMetricLocatedNetSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricLocatedNetSelectionUp.mk compactSource dyadicTolerance streamWindow
      regularReadback realSeal transport replay provenance nameCert =>
      [compactSource, dyadicTolerance, streamWindow, regularReadback, realSeal, transport,
        replay, provenance, nameCert]

def CompactMetricLocatedNetSelectionCarrier [AskSetup] [PackageSetup]
    (K D W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      compactMetricLocatedNetSelectionFields
          (CompactMetricLocatedNetSelectionUp.mk K D W R E H C P N) =
        [K, D, W, R, E, H, C, P, N] ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CompactMetricLocatedNetSelection_namecert_obligations [AskSetup] [PackageSetup]
    {K D W R E H C P N locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactMetricLocatedNetSelectionCarrier K D W R E H C P N bundle pkg ->
      Cont K D W ->
        Cont W R E ->
          Cont E N locatedRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row locatedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K D W ∧ Cont W R E ∧
                        Cont E N locatedRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactDyadicRoute windowReadbackRoute sealNameRoute provenancePkg namePkg
  obtain ⟨_kUnary, _dUnary, _wUnary, _rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _fieldsExact, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed eUnary nUnary sealNameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row locatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K D W ∧ Cont W R E ∧ Cont E N locatedRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead ⟨hsame_refl locatedRead, locatedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactDyadicRoute, windowReadbackRoute, sealNameRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, locatedUnary⟩

end BEDC.Derived.CompactMetricLocatedNetSelectionUp
