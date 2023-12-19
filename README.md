# Interactive Optimal Repairs (Protégé plugin)

To use this plugin, do the following steps:
1. Download Protégé from [https://protege.stanford.edu](https://protege.stanford.edu) and install it.
2. Build the bundle of this plugin with `sbt osgiBundle`.
3. Copy the jar file from `target` to the subfolder `plugins` of Protégé.
4. Run Protégé and activate the new tab from the menu *Window* → *Tabs* → *Interactive Optimal Repair*.

Instead of Steps 2 and 3, you can also download the bundle from https://github.com/francesco-kriegel/interactive-optimal-repairs/releases/download/v0.1.4/interactive-optimal-repairs-0.1.4.jar into the subfolder `plugins` of Protégé.

### MacOS Installer Script

As an alternative on MacOS, you can use the installer script https://raw.githubusercontent.com/francesco-kriegel/interactive-optimal-repairs/main/install-macos.sh to automatically download and configure Protégé, GraalVM JDK, and a bundle of this plugin.  First create a new folder, say `XYZ`, then download the aforementioned script into this folder, and run it in terminal.  More specifically, go to the folder `XYZ` and execute the script with `./install-mac.sh`. It might be necessary to first make it runnable by `chmod +x install-macos.sh`.

At the end of executing the installer script, Protégé including this plugin is started.  Subsequent starts can be made by the command `Protege-5.6.3/run.sh` when in terminal in the folder `XYZ`.  For some reason I do not know, the used version of Protégé does not shutdown completely; nevertheless, files of edited ontologies are properly saved to disk.  This has nothing to do with this plugin.  To force quit use the key combination `Control+C` in terminal.