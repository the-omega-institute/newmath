import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealIntervalHullUp [AskSetup] [PackageSetup]
    (realFamily stream readback dyadic approximation interval lower upper enclosure transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory realFamily ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
    UnaryHistory dyadic ∧ UnaryHistory approximation ∧ UnaryHistory interval ∧
      UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory enclosure ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory localName ∧ Cont realFamily stream readback ∧
            Cont readback dyadic approximation ∧ Cont lower upper interval ∧
              Cont approximation interval enclosure ∧ Cont enclosure transport replay ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace LocatedRealIntervalHullUp

theorem LocatedRealIntervalHullCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {realFamily stream readback dyadic approximation interval lower upper enclosure transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.LocatedRealIntervalHullUp realFamily stream readback dyadic approximation interval
        lower upper enclosure transport replay provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BEDC.Derived.LocatedRealIntervalHullUp realFamily stream readback dyadic approximation
              interval lower upper enclosure transport replay provenance localName bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.LocatedRealIntervalHullUp realFamily stream readback dyadic approximation
              interval lower upper enclosure transport replay provenance localName bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.LocatedRealIntervalHullUp realFamily stream readback dyadic approximation
              interval lower upper enclosure transport replay provenance localName bundle pkg ∧
            hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro accepted
  constructor
  · constructor
    · exact Exists.intro localName ⟨accepted, hsame_refl localName⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row source
    exact source
  · intro _row source
    exact source

end LocatedRealIntervalHullUp
end BEDC.Derived
