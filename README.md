# xtension_plugin
This python module is a part of XTension at https://MacHomeAutomation.com it provides for the low level communication between a plugin and the XTension host program. It also creates a high level interface to the protocol with all the objects and classes necessary to develop plugins.
This program is included in the release version of XTension and does not need to be included with each plugin. It is in the include path when a plugin is running with the included Python build and can be included into any plugin by adding this to the include section:

```
from xtension_plugin.xtension_constants import *
from xtension_plugin.xtension_plugin import *
```
