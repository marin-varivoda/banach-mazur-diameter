import BMLean.Tables
import BMLean.Data.Hub020

namespace BMC

theorem hubOk_020 : hubChunkOk (parseRows BMD.hub020) = true := by native_decide

end BMC
