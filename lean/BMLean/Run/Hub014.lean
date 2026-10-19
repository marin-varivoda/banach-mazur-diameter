import BMLean.Tables
import BMLean.Data.Hub014

namespace BMC

theorem hubOk_014 : hubChunkOk (parseRows BMD.hub014) = true := by native_decide

end BMC
