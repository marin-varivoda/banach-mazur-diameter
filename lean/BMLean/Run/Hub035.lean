import BMLean.Tables
import BMLean.Data.Hub035

namespace BMC

theorem hubOk_035 : hubChunkOk (parseRows BMD.hub035) = true := by native_decide

end BMC
