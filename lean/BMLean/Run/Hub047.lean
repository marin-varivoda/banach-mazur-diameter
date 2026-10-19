import BMLean.Tables
import BMLean.Data.Hub047

namespace BMC

theorem hubOk_047 : hubChunkOk (parseRows BMD.hub047) = true := by native_decide

end BMC
