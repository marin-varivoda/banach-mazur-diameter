import BMLean.Tables
import BMLean.Data.Hub006

namespace BMC

theorem hubOk_006 : hubChunkOk (parseRows BMD.hub006) = true := by native_decide

end BMC
