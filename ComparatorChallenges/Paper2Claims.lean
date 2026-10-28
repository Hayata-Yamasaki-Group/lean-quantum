import ComparatorChallenges.Paper2Headline
import Quantum.QuantumEntropy.GourResource.GeneralizedStein
import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Petz.HiaiPetz.HiaiPetzProvider
import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.LiebAndoProvider
import Quantum.QuantumEntropy.RenyiDPI.Petz.SelectedProvider
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.HiaiPetzProvider
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.LiebAndoProvider
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.SelectedProvider
import Quantum.QuantumEntropy.UmegakiDPI.Interface
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumEntropy.UmegakiDPI.Provider
import Quantum.QuantumEntropy.UmegakiDPI.SelectedProvider
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.HPAdapter
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.FromRenyi.GSLCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.SRAdapter
import Quantum.QuantumEntropy.VonNeumann.SSA
import Quantum.TraceInequality.HansenPedersen.HansenPedersenAdapter
import Quantum.TraceInequality.HiaiPetz.Interface.OutputSupport
import Quantum.TraceInequality.HiaiPetz.SelectedProvider
import Quantum.TraceInequality.Loewner.LoewnerAdapter
import Quantum.TraceInequality.Loewner.UnitInterval.IntegralToOperatorMonotone
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.PublicCorrespondence

/-! Generated index of the public claims.
35 roots: 31 headline, 4 support; 19 theorems, 16 definitions/structures.
#check verifies existence and elaboration, not axiom dependencies. -/

-- P2-R001 (headline, theorem)
#check GourResource.gsl_y54
-- P2-R002 (headline, theorem)
#check GourResource.gsl_y53
-- P2-R003 (headline, theorem)
#check GourResource.gsl_y55
-- P2-R004 (headline, theorem)
#check VonNeumann.strongSubadditivity_of_state
-- P2-R005 (headline, theorem)
#check ProofNet.strictDPIEquivalences
-- P2-R006 (headline, theorem)
#check ProofNet.outputSupportDPIEquivalences
-- P2-R007 (headline, def)
#check ProofNet.selectedProvider
-- P2-R008 (headline, def)
#check ProofNet.hansenPedersenProvider
-- P2-R009 (headline, structure)
#check RenyiDPI.SandwichedSide
-- P2-R010 (headline, structure)
#check RenyiDPI.PetzSide
-- P2-R011 (headline, def)
#check RenyiDPI.sandwichedLiebAndoProvider
-- P2-R012 (headline, def)
#check RenyiDPI.sandwichedHiaiPetzProvider
-- P2-R013 (headline, def)
#check RenyiDPI.petzLiebAndoProvider
-- P2-R014 (headline, def)
#check RenyiDPI.petzHiaiPetzProvider
-- P2-R015 (headline, def)
#check RenyiDPI.selectedSandwichedProvider
-- P2-R016 (headline, def)
#check RenyiDPI.selectedPetzProvider
-- P2-R017 (headline, theorem)
#check UmegakiDPI.monotoneOnPosDef_of_sandwiched
-- P2-R018 (headline, theorem)
#check UmegakiDPI.monotoneOnPosDef_of_petz
-- P2-R019 (headline, theorem)
#check UmegakiDPI.monotoneOnPosDef
-- P2-R020 (support, theorem)
#check UmegakiDPI.monotoneOnNonNeg
-- P2-R021 (support, theorem)
#check ComparatorChallenges.loewnerUnitIntervalFourConditions
-- P2-R022 (support, theorem)
#check Quantum.TraceInequality.Loewner.unitIntervalPickExtension_iff_integralRep
-- P2-R023 (support, theorem)
#check Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_of_integralRep
-- P2-R024 (headline, structure)
#check ProofNet.Provider
-- P2-R025 (headline, def)
#check ProofNet.loewnerProvider
-- P2-R026 (headline, theorem)
#check ProofNet.strictDPIEquivalences_via_hansenPedersen
-- P2-R027 (headline, theorem)
#check ProofNet.outputSupportDPIEquivalences_via_hansenPedersen
-- P2-R028 (headline, theorem)
#check ProofNet.strictDPIEquivalences_via_loewner
-- P2-R029 (headline, theorem)
#check ProofNet.outputSupportDPIEquivalences_via_loewner
-- P2-R030 (headline, structure)
#check UmegakiDPI.Provider
-- P2-R031 (headline, def)
#check UmegakiDPI.selectedProvider
-- P2-R032 (headline, def)
#check UmegakiDPI.sandwichedRenyiProvider
-- P2-R033 (headline, def)
#check UmegakiDPI.hiaiPetzProvider
-- P2-R034 (headline, theorem)
#check UmegakiDPI.monotoneOnPosDef_via_sandwichedRenyi
-- P2-R035 (headline, theorem)
#check UmegakiDPI.monotoneOnPosDef_via_hiaiPetz
