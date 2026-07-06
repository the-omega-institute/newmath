import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ImplicitFunctionTheoremUp

namespace BEDC.Derived.ImplicitFunctionTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ImplicitFunctionTheoremCarrier [AskSetup] [PackageSetup]
    (equation derivative inverse newton sealRow graph transport replay provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig
  UnaryHistory equation ∧ UnaryHistory derivative ∧ UnaryHistory inverse ∧
    UnaryHistory newton ∧ UnaryHistory sealRow ∧ UnaryHistory graph ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont equation derivative inverse ∧
          Cont inverse newton sealRow ∧ Cont sealRow graph transport ∧
            Cont replay provenance localName ∧ PkgSig bundle provenance pkg

theorem ImplicitFunctionTheoremCarrier_newton_completion_handoff [AskSetup] [PackageSetup]
    {equation derivative inverse newton sealRow graph transport replay provenance localName
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ImplicitFunctionTheoremCarrier equation derivative inverse newton sealRow graph transport
        replay provenance localName bundle pkg →
      Cont newton sealRow endpointRead →
        PkgSig bundle provenance pkg →
          SemanticNameCert
              (fun row : BHist =>
                ImplicitFunctionTheoremCarrier equation derivative inverse newton sealRow graph
                  transport replay provenance localName bundle pkg ∧ hsame row localName)
              (fun row : BHist => hsame row localName ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row localName ∧
                  Cont newton sealRow endpointRead)
              hsame ∧
            UnaryHistory equation ∧ UnaryHistory derivative ∧ UnaryHistory inverse ∧
              UnaryHistory newton ∧ UnaryHistory sealRow ∧ UnaryHistory graph ∧
                UnaryHistory endpointRead ∧ Cont equation derivative inverse ∧
                  Cont inverse newton sealRow ∧ Cont newton sealRow endpointRead ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier newtonSealEndpoint provenancePkg'
  have carrierPacket :
      ImplicitFunctionTheoremCarrier equation derivative inverse newton sealRow graph transport
        replay provenance localName bundle pkg :=
    carrier
  obtain ⟨equationUnary, derivativeUnary, inverseUnary, newtonUnary, sealUnary,
    graphUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    equationDerivativeInverse, inverseNewtonSeal, _sealGraphTransport,
    _replayProvenanceLocalName, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed newtonUnary sealUnary newtonSealEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ImplicitFunctionTheoremCarrier equation derivative inverse newton sealRow graph
              transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row localName ∧
              Cont newton sealRow endpointRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName ⟨carrierPacket, hsame_refl localName⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport localNameUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, source.right, newtonSealEndpoint⟩
    }
  exact
    ⟨cert, equationUnary, derivativeUnary, inverseUnary, newtonUnary, sealUnary,
      graphUnary, endpointUnary, equationDerivativeInverse, inverseNewtonSeal,
      newtonSealEndpoint, provenancePkg'⟩

end BEDC.Derived.ImplicitFunctionTheoremUp
