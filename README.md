# Interactive Optimal Repairs (Protégé plugin)

### MacOS Installer Script

On MacOS you can use the installer script https://raw.githubusercontent.com/francesco-kriegel/interactive-optimal-repairs/main/install-macos.sh to automatically download and configure Protégé, GraalVM JDK, and a bundle of this plugin.  First create a new folder, say `XYZ`, then download the aforementioned script into this folder, and run it in terminal.  More specifically, go to the folder `XYZ` and execute the script with `./install-mac.sh`. It might be necessary to first make it runnable by `chmod +x install-macos.sh`.

At the end of executing the installer script, Protégé including this plugin is started.  Subsequent starts can be made by the command `Protege-5.6.3/run.sh` when in terminal in the folder `XYZ`.  For some reason I do not know, the used version of Protégé does not shutdown completely; nevertheless, files of edited ontologies are properly saved to disk.  This has nothing to do with this plugin.  To force quit use the key combination `Control+C` in terminal.

### Building from Source 

1. Download Protégé from https://protege.stanford.edu and unpack it (tested with the platform-independent variant of Protégé 5.6.3).
2. The source code of this plugin depends on the source code of Protégé.  Since no artifacts of the dependency version have been published to any publicly accessible Maven repository, it is mandatory to manually install the source code to your machine.  To this end, clone the git repository of Protégé from https://github.com/protegeproject/protege and install it to your local Maven repository with `mvn install -DskipTests` (tested with version 5.6.3).
3. Clone this git repository and build the bundle of this plugin with `sbt osgiBundle` (tested with GraalVM 21.0.1+12.1 and sbt 1.9.8).
4. Copy the jar file from `target` to the subfolder `plugins` of Protégé (from Step 1).
5. If you want to work with large ontologies, then increase the memory limit of Protégé by adding the line `max_heap_size=16G` to the file `conf/jvm.conf` of Protégé (from Step 1).
6. Run Protégé and activate the new tab from the menu *Window* → *Tabs* → *Interactive Optimal Repair* (tested with GraalVM 21.0.1+12.1).

Instead of Steps 2-4, you can also download the bundle from https://github.com/francesco-kriegel/interactive-optimal-repairs/releases/download/v0.1.4/interactive-optimal-repairs-0.1.4.jar into the subfolder `plugins` of Protégé.

