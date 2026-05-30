import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRealIntervalHullUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealIntervalHullCarrier [AskSetup] [PackageSetup]
    (realNames windows readbacks dyadic approximants interval lower upper enclosure transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory realNames ∧ UnaryHistory windows ∧ UnaryHistory readbacks ∧
    UnaryHistory dyadic ∧ UnaryHistory approximants ∧ UnaryHistory interval ∧
      UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory enclosure ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory localName ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem LocatedRealIntervalHullNamecertObligations [AskSetup] [PackageSetup]
    {realNames windows readbacks dyadic approximants interval lower upper enclosure transport
      replay provenance localName endpointRead hullRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealIntervalHullCarrier realNames windows readbacks dyadic approximants interval lower
        upper enclosure transport replay provenance localName bundle pkg →
      Cont interval lower endpointRead →
        Cont endpointRead upper hullRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle localName pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row hullRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row realNames ∨ hsame row windows ∨ hsame row readbacks ∨
                      hsame row dyadic ∨ hsame row approximants ∨ hsame row interval ∨
                        hsame row hullRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory endpointRead ∧ UnaryHistory hullRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier intervalLowerEndpoint endpointUpperHull provenancePkg localNamePkg
  obtain ⟨_realNamesUnary, _windowsUnary, _readbacksUnary, _dyadicUnary,
    _approximantsUnary, intervalUnary, lowerUnary, upperUnary, _enclosureUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportReplayProvenance, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalUnary lowerUnary intervalLowerEndpoint
  have hullUnary : UnaryHistory hullRead :=
    unary_cont_closed endpointUnary upperUnary endpointUpperHull
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hullRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row realNames ∨ hsame row windows ∨ hsame row readbacks ∨
              hsame row dyadic ∨ hsame row approximants ∨ hsame row interval ∨
                hsame row hullRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro hullRead ⟨hsame_refl hullRead, hullUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, endpointUnary, hullUnary⟩

end BEDC.Derived.LocatedRealIntervalHullUp
