#!/usr/local/bin/perl
###########################################################################################
# Copyright (c) 2008-2010 Matthew Ballance and others.
# All rights reserved. This program and the accompanying materials
# are made available under the terms of the Eclipse Public License v1.0
# which accompanies this distribution, and is available at
# http://www.eclipse.org/legal/epl-v10.html
#
# Contributors:
#     Steven Dawson - had to do something to help out
#    
###########################################################################################
# This script is used to create a .project and .svproject files for a given project.
###########################################################################################

use strict;
my $debug = 0;

# Step1: 
# Replace $project_name with something unique
# Example:
# my $project_name = $ENV{CHIP_NAME} . "_" . "$ENV{USER}";
my $project_name = "555_builderb_01";

# Step 2: Environment Variables:
my %hash_of_variables = (
   # Replace this with your unique set of environment variables
   # It's reasonably easy to suck environment variables into perl, use
   # $ENV{SOMENAME} if you want something specific
   'CHIP', "\${PROJECT_LOC}"
);

# Step 3: Resource filters
# Add a list of directories that you want Eclipse to ignore
# Examples are compiled output, log files, synthesis output directories etc.
my @ignored_directories = ("log", "directory_to_ignore");

# Replace this with the list of files.f's that you have
my @list_of_argument_files = ("\${CHIP}/sim/files.f");

###########################################################################################
# This sub-routine makes strings provided by user something that XML seems to like
# I am sure there are pre-packages perl modules for this.
###########################################################################################
sub MakeStringXML_Happy  {
   my $instring = @_[0];   # grab the string
   
   $instring =~ s/\{/\%7B/;   # { -> %7B
   $instring =~ s/\}/\%7D/;   # } -> %7D
   
   return ($instring);
}


###########################################################################################
# Main Routine
###########################################################################################

# Start by creating .project
open(DOT_PROJECT , "> .project")    or die "cannot open > .project $!";

print DOT_PROJECT "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
print DOT_PROJECT " <projectDescription>\n";
print DOT_PROJECT " 	<name>$project_name</name>\n";     # Project name inserted here
print DOT_PROJECT " 	<comment></comment>\n";
print DOT_PROJECT " 	<projects>\n";
print DOT_PROJECT " 	</projects>\n";
print DOT_PROJECT " 	<buildSpec>\n";
print DOT_PROJECT " 		<buildCommand>\n";
print DOT_PROJECT " 			<name>net.sf.sveditor.core.SVProjectBuilder</name>\n";
print DOT_PROJECT " 			<arguments>\n";
print DOT_PROJECT " 			</arguments>\n";
print DOT_PROJECT " 		</buildCommand>\n";
print DOT_PROJECT " 	</buildSpec>\n";
print DOT_PROJECT " 	<natures>\n";
print DOT_PROJECT " 		<nature>net.sf.sveditor.core.SVNature</nature>\n";
print DOT_PROJECT " 	</natures>\n";
print DOT_PROJECT " 	<filteredResources>\n";
foreach my $dir_to_ignore (@ignored_directories)  {
print DOT_PROJECT " 		<filter>\n";
print DOT_PROJECT " 			<id>1390544911481</id>\n";
print DOT_PROJECT " 			<name></name>\n";
print DOT_PROJECT " 			<type>30</type>\n";
print DOT_PROJECT " 			<matcher>\n";
print DOT_PROJECT " 				<id>org.eclipse.ui.ide.multiFilter</id>\n";
print DOT_PROJECT " 				<arguments>1.0-name-matches-false-false-$dir_to_ignore</arguments>\n"; # dir_to_ignore inserted here
print DOT_PROJECT " 			</matcher>\n";
print DOT_PROJECT " 		</filter>\n";
}
print DOT_PROJECT " 	</filteredResources>\n";
print DOT_PROJECT " 	<variableList>\n";
foreach my $variable (keys %hash_of_variables)  {
print DOT_PROJECT " 		<variable>\n";
print DOT_PROJECT " 			<name>$variable</name>\n";
print DOT_PROJECT " 			<value>" . MakeStringXML_Happy($hash_of_variables{$variable}) . "</value>\n"; # insert variables here
print DOT_PROJECT " 		</variable>\n";
}
print DOT_PROJECT " 	</variableList>\n";
print DOT_PROJECT " </projectDescription>\n";
  
close (DOT_PROJECT);

  
# Now create .svproject
open(DOT_SV_PROJECT , "> .svproject")    or die "cannot open > .svproject $!";
print DOT_SV_PROJECT "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n";
print DOT_SV_PROJECT "<svproject>\n";
print DOT_SV_PROJECT "<defines/>\n";
print DOT_SV_PROJECT "<includePaths/>\n";
print DOT_SV_PROJECT "<buildPaths/>\n";
print DOT_SV_PROJECT "<pluginPaths>\n";
print DOT_SV_PROJECT "<pluginPath path=\"net.sf.sveditor.sv_builtin\"/>\n";
print DOT_SV_PROJECT "</pluginPaths>\n";
print DOT_SV_PROJECT "<libraryPaths/>\n";
print DOT_SV_PROJECT "<argFilePaths>\n";
foreach my $argfile (@list_of_argument_files)  {
print DOT_SV_PROJECT "<argFilePath path=\"" . $argfile . "\"/>\n";   # insert argument files
}
print DOT_SV_PROJECT "</argFilePaths>\n";
print DOT_SV_PROJECT "<sourceCollections/>\n";
print DOT_SV_PROJECT "<projectRefs/>\n";
print DOT_SV_PROJECT "</svproject>\n";
print DOT_SV_PROJECT "\n";
close (DOT_SV_PROJECT);

print "Eclipse project files '.project' and '.svproject' created.  Open Eclipse, File>Import>Existing Projects into Workspace, browse to this directory and hit OK!\n";