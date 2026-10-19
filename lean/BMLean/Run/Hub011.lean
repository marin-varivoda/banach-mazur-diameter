import BMLean.Tables
import BMLean.Data.Hub011

namespace BMC

theorem hubOk_011 : hubChunkOk (parseRows BMD.hub011) = true := by native_decide

end BMC
