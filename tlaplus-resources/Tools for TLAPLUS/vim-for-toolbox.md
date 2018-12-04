Hi Thomas, Hi Yoriyasu,

while Yoriyasu's way to install vrapper obviously works, this way to install plugins has been deprecated by Eclipse and might break your Toolbox in subtle ways. If you ever run into problems, here's how you install plugins manually:

1) Start the toolbox from the command line with the two parameters "./toolbox -console -consoleLog" to activate its console
2) In the console ("osgi>" prompt), activate the functionality to install plugins: "start org.eclipse.equinox.p2.console"

3) Add the p2 repository a.k.a update site of the plugin, e.g. "provaddrepo http://vrapper.sourceforge.net/update-site/stable"

4) List the available "installation units" (IU) in the update site "provlg http://vrapper.sourceforge.net/update-site/stable"

5) Install the top-level IU with "provinstall net.sourceforge.vrapper.feature.group 0.72.0 DefaultProfile"
provinstall triggers a (modal) dialog in the Toolbox. Accept it and restart the Toolbox.

Cheers

Markus

`./toolbox -console -consoleLog`
`start org.eclipse.equinox.p2.console`
`provaddrepo http://vrapper.sourceforge.net/update-site/stable`
`provlg http://vrapper.sourceforge.net/update-site/stable`
`provinstall net.sourceforge.vrapper.feature.group 0.72.0 DefaultProfile` % replace 0.72.0 by the actual version