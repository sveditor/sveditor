// Generates the WiX XML necessary to install a directory tree.
var g_shell = new ActiveXObject("WScript.Shell");
var g_fs = new ActiveXObject("Scripting.FileSystemObject");
if (WScript.Arguments.length != 2)
{
    WScript.Echo("Usage: cscript.exe generate-install-script.js <rootFolder> <outputXMLFile>");
    WScript.Quit(1);
}

var rootDir = WScript.Arguments.Item(0);
var outFile = WScript.Arguments.Item(1);
var baseFolder = g_fs.GetFolder(rootDir);
var componentIds = new Array();

WScript.Echo("Generating " + outFile + "...");

var f = g_fs.CreateTextFile(outFile, true);
f.WriteLine("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>");
f.WriteLine("<Include>");
f.WriteLine("  <Directory Id=\"TARGETDIR\" Name=\"SourceDir\">");
f.Write(getDirTree(rootDir, "", 1, baseFolder, componentIds));
f.WriteLine("  </Directory>");
f.WriteLine("  <Feature Id=\"DefaultFeature\" Level=\"1\" ConfigurableDirectory=\"TARGETDIR\">");
for (var i=0; i<componentIds.length; i++)
{
    f.WriteLine("    <ComponentRef Id=\"C__" + componentIds[i] + "\" />");
}
f.WriteLine("  </Feature>");
f.WriteLine("</Include>");
f.Close();

// recursive method to extract information for a folder
function getDirTree(root, xml, indent, baseFolder, componentIds)
{
    var fdrFolder = null;
    try
    {
        fdrFolder = g_fs.GetFolder(root);
    }
    catch (e)
    {
        return;
    }

    // indent the xml
    var space = "";
    for (var i=0; i<indent; i++)
        space = space + "  ";

    if (fdrFolder != baseFolder)
    {
        var directoryId = "_" + FlatFormat(GetGuid());

        xml = xml + space + "<Directory Id=\"" + directoryId +"\"";
        xml = xml + " Name=\"" + fdrFolder.ShortName.toUpperCase() + "\"";
        xml = xml + " LongName=\"" + fdrFolder.Name + "\">\r\n";
    }

    var componentGuid = GetGuid();
    var componentId = FlatFormat(componentGuid);

    xml = xml + space + "  <Component Id=\"C__" + componentId + "\""
              + " Guid=\"" + componentGuid + "\">\r\n";
              
	var enumFiles = new Enumerator(fdrFolder.Files);
	for (;!enumFiles.atEnd(); enumFiles.moveNext()) {
// <File Id="CPL.TXT" Name="CPL.TXT" KeyPath="yes" DiskId="1" Source="SourceDir\File\CPL.TXT" />	
      xml = xml + space + "    <File DiskId=\"1\" "
              + "Id=\"" + MkId(enumFiles.item().Name) + "\" "
              + "Name=\"" + enumFiles.item().Name + "\" "
              + "Source=\"SourceDir" + fdrFolder.Path.substring(baseFolder.Path.length) + "\\" +enumFiles.item() + "\"/>\r\n";
	}
	/*              
    xml = xml + space + "    <FileGroup filter=\"*.*\" Prefix=\""
              + componentId + "\" src=\"$(var.redist_folder)"
              + fdrFolder.Path.substring(baseFolder.Path.length)
              + "\" DiskId=\"1\"/>\r\n";
     */
    xml = xml + space + "  </Component>\r\n";

    componentIds[componentIds.length] = componentId;

    var enumSubFolders = new Enumerator(fdrFolder.SubFolders);
	WScript.Echo("Folder: ", fdrFolder);        

    var depth = indent + 1;
    for (;!enumSubFolders.atEnd();enumSubFolders.moveNext())
    {
        var subfolder = enumSubFolders.item();
//		WScript.Echo("File: ", subfolder);        
        xml = getDirTree(enumSubFolders.item().Path, xml, depth, baseFolder, componentIds);
    }

    if (fdrFolder != baseFolder)
    {
        xml = xml + space + "</Directory>\r\n";
    }

    return xml;
}

function GetGuid() {
  var n = [36], s = [36], itoh = [];
  
  itoh[0] = '0';
  itoh[1] = '1';
  itoh[2] = '2';
  itoh[3] = '3';
  itoh[4] = '4';
  itoh[5] = '5';
  itoh[6] = '6';
  itoh[7] = '7';
  itoh[8] = '8';
  itoh[9] = '9';
  itoh[10] = 'A';
  itoh[11] = 'B';
  itoh[12] = 'C';
  itoh[13] = 'D';
  itoh[14] = 'E';
  itoh[15] = 'F';
  
  // Make array of random hex digits. The UUID only has 32 digits in it, but we
  // allocate an extra items to make room for the '-'s we'll be inserting.
  for (var i = 0; i <36; i++) {
    n[i] = Math.floor(Math.random()*0x10);
  }
 
  // Conform to RFC-4122, section 4.4
  n[14] = 4;  // Set 4 high bits of time_high field to version
  n[19] = (n[19] & 0x3) | 0x8;  // Specify 2 high bits of clock sequence
 
  // Convert to hex chars
  for (var i = 0; i <36; i++) {
    s[i] = itoh[n[i]];
  } 
 
  // Insert '-'s
  s[8] = s[13] = s[18] = s[23] = '-';
  
  return s.join('').toUpperCase();
}

// Generate a new GUID by calling uuidgen
/*
function GetGuid()
{
    var sysEnv = g_shell.Environment("SYSTEM");
    var oExec = g_shell.Exec(sysEnv("VS71COMNTOOLS") + "uuidgen.exe");
    var input = "";

    while (!oExec.StdOut.AtEndOfStream)
    {
        input += oExec.StdOut.Read(1);
    }
    return input.substring(0,36).toUpperCase();
}
*/

// Convert a GUID from this format
//   7e70e5e5-ce19-4270-a740-223a09796433
// to this format:
//   7E70E5E5CE194270A740223A09796433
function FlatFormat(guid)
{
    var re = /-/g;
    return guid.toUpperCase().replace(re, "");
}

function MkId(name)
{
  if (name.charAt(0) == '.') {
    return "_" + name.substring(1);
  } else {
    return name;
  }
}
