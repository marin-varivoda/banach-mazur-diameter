import BMLean.Tables
import BMLean.Data.Hub053

namespace BMC

theorem hubOk_053 : hubChunkOk (parseRows BMD.hub053) = true := by native_decide

end BMC
