import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DedekindCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DedekindCutCarrier [AskSetup] [PackageSetup]
    (lower upper inhabited rounded located disjoint embedding transport routes provenance nameCert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory inhabited ∧ UnaryHistory rounded ∧
    UnaryHistory located ∧ UnaryHistory disjoint ∧ UnaryHistory embedding ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont lower upper inhabited ∧ Cont inhabited rounded located ∧
          Cont located disjoint embedding ∧ Cont embedding transport routes ∧
            Cont routes nameCert provenance ∧ PkgSig bundle provenance pkg

theorem DedekindCutCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {lower upper inhabited rounded located disjoint embedding transport routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              DedekindCutCarrier lower upper inhabited rounded located disjoint embedding
                transport routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ Cont lower upper inhabited)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory inhabited ∧
          UnaryHistory rounded ∧ UnaryHistory located ∧ UnaryHistory disjoint ∧
            UnaryHistory embedding ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
              UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont lower upper inhabited ∧
                Cont inhabited rounded located ∧ Cont located disjoint embedding ∧
                  Cont embedding transport routes ∧ Cont routes nameCert provenance ∧
                    PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨lowerUnary, upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
    embeddingUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, lowerUpper,
    inhabitedRounded, locatedDisjoint, embeddingTransport, routesNameCert, provenancePkg⟩ :=
      carrier
  have carrierRows :
      DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport routes
        provenance nameCert bundle pkg :=
    ⟨lowerUnary, upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
      embeddingUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, lowerUpper,
      inhabitedRounded, locatedDisjoint, embeddingTransport, routesNameCert, provenancePkg⟩
  have sourceProvenance :
      (fun row : BHist =>
        hsame row provenance ∧
          DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport
            routes provenance nameCert bundle pkg) provenance := by
    exact ⟨hsame_refl provenance, carrierRows⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row provenance ∧
            DedekindCutCarrier lower upper inhabited rounded located disjoint embedding transport
              routes provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro provenance sourceProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              DedekindCutCarrier lower upper inhabited rounded located disjoint embedding
                transport routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ Cont lower upper inhabited)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact ⟨source.left, lowerUpper⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, lowerUnary, upperUnary, inhabitedUnary, roundedUnary, locatedUnary, disjointUnary,
      embeddingUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, lowerUpper,
      inhabitedRounded, locatedDisjoint, embeddingTransport, routesNameCert, provenancePkg⟩

end BEDC.Derived.DedekindCutUp
