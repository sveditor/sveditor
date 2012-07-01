/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Natural Docs - initial implementation
 *     Armond Paiva - repurposed from Natural Docs for use in SVEditor
 *    
 * This class is part of a Java port of the natural docs native format 
 * parser. The following Natural Docs(ND) Perl packages were 
 * ported in varying degrees:
 * 		NaturalDocs::Parser, NaturalDocs::Parser::Native, 
 * 		NaturalDocs::Parser::ParsedTopic, NaturalDocs::NDMarkup
 *     
 ****************************************************************************
 * Original Natural Docs License:
 *
 *	This file is part of Natural Docs, which is Copyright (c) 2003-2010 Greg Valure
 *	Natural Docs is licensed under version 3 of the GNU Affero General Public License (AGPL)
 *	Refer to License.txt for the complete details
 *	
 ****************************************************************************/

package net.sf.sveditor.core.docs ;

import java.util.regex.Pattern ;

public class DocCommentCleaner {
	
	public static String TAB_EXPANSION = "   " ;
	
	private enum Uniformity { DONT_KNOW, IS_UNIFORM, IS_UNIFORM_IF_AT_END, IS_NOT_UNIFORM } ;

	//
	//   Function: CleanComment
	//
	//   Removes any extraneous formatting and whitespace from the comment.  Eliminates comment boxes, horizontal lines, trailing
	//   whitespace from lines, and expands all tab characters.  It keeps leading whitespace, though, since it may be needed for
	//   example code, and blank lines, since the original line numbers are needed.
	//
	
	public static void clean(String[] lines) {
		
		Uniformity leftSide = Uniformity.DONT_KNOW ;
		Uniformity rightSide = Uniformity.DONT_KNOW ;
		
//	    my $tabLength = NaturalDocs::Settings->TabLength();
		
//		String tabExpansion = "   " ;
		int index = 0 ;
		boolean inCodeSection = false ;
		
		while(index < lines.length) {
		
	        // Strip trailing whitespace from the original.
			//
			lines[index] = lines[index].replaceAll("[ \\t]+$", "") ;
			
//	        # Expand tabs in the original.  This method is almost six times faster than Text::Tabs' method.
//	
//	        my $tabIndex = index($commentLines->[$index], "\t");
//	
//	        while ($tabIndex != -1)
//	            {
//	            substr( $commentLines->[$index], $tabIndex, 1, ' ' x ($tabLength - ($tabIndex % $tabLength)) );
//	            $tabIndex = index($commentLines->[$index], "\t", $tabIndex);
//	            };
			
			lines[index] = lines[index].replaceAll("\\t", TAB_EXPANSION) ;

//	        # Make a working copy and strip leading whitespace as well.  This has to be done after tabs are expanded because
//	        # stripping indentation could change how far tabs are expanded.
//	
//	        my $line = $commentLines->[$index];
//	        $line =~ s/^ +//;
			
			String line = lines[index] ;
			
	        // If the line is blank...
			//
			if(line.length()==0) {
	            // If we have a potential vertical line, this only acceptable if it's at the end of the comment.
	            if (leftSide == Uniformity.IS_UNIFORM)
	                {  leftSide = Uniformity.IS_UNIFORM_IF_AT_END ; }
	            if (rightSide == Uniformity.IS_UNIFORM)
	                {  rightSide = Uniformity.IS_UNIFORM_IF_AT_END ; }
            }

	        // If there's at least four symbols in a row, it's a horizontal line.  The second regex supports differing edge characters.  It
	        // doesn't matter if any of this matches the left and right side symbols.  The length < 256 is a sanity check, because that
	        // regexp has caused the perl regexp engine to choke on an insane line someone sent me from an automatically generated
	        // file.  It had over 10k characters on the first line, and most of them were 0x00.
			//
			else if (line.matches("^([^a-zA-Z0-9 ])\\1{3,}$") ||
					 ((line.length() < 256) &&
							 line.matches("^([^a-zA-Z0-9 ])\\1*([^a-zA-Z0-9 ])\\2{3,}([^a-zA-Z0-9 ])\\3*$/"))) {
			
	            // Ignore it.  This has no effect on the vertical line detection.  We want to keep it in the output though in case it was
	            // in a code section.

	        // If the line is not blank or a horizontal line...
			//
			} else {
	        	
	            // More content means any previous blank lines are no longer tolerated in vertical line detection.  They are only
	            // acceptable at the end of the comment.
	
	            if (leftSide == Uniformity.IS_UNIFORM_IF_AT_END)
	                {  leftSide = Uniformity.IS_NOT_UNIFORM;  }
	            if (rightSide == Uniformity.IS_UNIFORM_IF_AT_END)
	                {  rightSide = Uniformity.IS_NOT_UNIFORM;  }


//	            # Detect vertical lines.  Lines are only lines if they are followed by whitespace or a connected horizontal line.
//	            # Otherwise we may accidentally detect lines from short comments that just happen to have every first or last
//	            # character the same.
//	
//	            if ($leftSide != IS_NOT_UNIFORM)
//	                {
//	                if ($line =~ /^([^a-zA-Z0-9])\1*(?: |$)/)
//	                    {
//	                    if ($leftSide == DONT_KNOW)
//	                        {
//	                        $leftSide = IS_UNIFORM;
//	                        $leftSideChar = $1;
//	                        }
//	                    else # ($leftSide == IS_UNIFORM)  Other choices already ruled out.
//	                        {
//	                        if ($leftSideChar ne $1)
//	                            {  $leftSide = IS_NOT_UNIFORM;  };
//	                        };
//	                    }
//	                # We'll tolerate the lack of symbols on the left on the first line, because it may be a
//	                # /* Function: Whatever
//	                #  * Description.
//	                #  */
//	                # comment which would have the leading /* blanked out.
//	                elsif ($index != 0)
//	                    {
//	                    $leftSide = IS_NOT_UNIFORM;
//	                    };
//	                };
//	
//	            if ($rightSide != IS_NOT_UNIFORM)
//	                {
//	                if ($line =~ / ([^a-zA-Z0-9])\1*$/)
//	                    {
//	                    if ($rightSide == DONT_KNOW)
//	                        {
//	                        $rightSide = IS_UNIFORM;
//	                        $rightSideChar = $1;
//	                        }
//	                    else # ($rightSide == IS_UNIFORM)  Other choices already ruled out.
//	                        {
//	                        if ($rightSideChar ne $1)
//	                            {  $rightSide = IS_NOT_UNIFORM;  };
//	                        };
//	                    }
//	                else
//	                    {
//	                    $rightSide = IS_NOT_UNIFORM;
//	                    };
//	                };
//	
//	            # We'll remove vertical lines later if they're uniform throughout the entire comment.
	            
            } 
			
        	index++ ;
        }
	
	
	    if (leftSide == Uniformity.IS_UNIFORM_IF_AT_END)
	        {  leftSide = Uniformity.IS_UNIFORM;  }
	    if (rightSide == Uniformity.IS_UNIFORM_IF_AT_END)
	        {  rightSide = Uniformity.IS_UNIFORM;  }
	
	    index = 0;
	    inCodeSection = false ;
	    
	    while(index < lines.length) {
	    
	        // Clear horizontal lines only if we're not in a code section.
	    	//
	        if (lines[index].matches("^ *([^a-zA-Z0-9 ])\\1{3,}") ||
	            ( lines[index].length() < 256 &&
	              lines[index].matches("^ *([^a-zA-Z0-9 ])\\1*([^a-zA-Z0-9 ])\\2{3,}([^a-zA-Z0-9 ])\\3*$" )))
	        	{
	        	if (!inCodeSection)
	        		{  lines[index] = "" ;  }
	        	}
	
	        else {
		        // Clear vertical lines.
	
		        if (leftSide == Uniformity.IS_UNIFORM) {
		            // This works because every line should either start this way, be blank, or be the first line that doesn't start with a
		            // symbol.
		            lines[index].replace("^ *([^a-zA-Z0-9 ])\\1*","") ;
	            }
	
		        if (rightSide == Uniformity.IS_UNIFORM) {
		            lines[index].replace(" *([^a-zA-Z0-9 ])\\1*$","") ;
	            }
	
		        // Clear horizontal lines again if there were vertical lines.  This catches lines that were separated from the verticals by
		        // whitespace.
	
		        if ((leftSide == Uniformity.IS_UNIFORM || rightSide == Uniformity.IS_UNIFORM) && !inCodeSection) {
		            lines[index].replace("^ *([^a-zA-Z0-9 ])\\1{3,}$","") ;
		            lines[index].replace("^ *([^a-zA-Z0-9 ])\\1*([^a-zA-Z0-9 ])\\2{3,}([^a-zA-Z0-9 ])\\3*$","") ;
	            }
	
		        // Check for the start and end of code sections.  Note that this doesn't affect vertical line removal.
		        //
	        	Pattern patternCodeStart = Pattern.compile("^ *\\( *(?:(?:start|begin)? +)?(?:table|code|example|diagram) *\\)$", Pattern.CASE_INSENSITIVE ) ;
		        Pattern patternCodeEnd = Pattern.compile("^ *\\( *(?:end|finish|done)(?: +(?:table|code|example|diagram))? *\\)$", Pattern.CASE_INSENSITIVE) ;
		        if (!inCodeSection &&
		        		patternCodeStart.matcher(lines[index]).matches()) {
		        	inCodeSection = true ;
	        	}
		        else if (inCodeSection && patternCodeEnd.matcher(lines[index]).matches()) { 
		        	 inCodeSection = false ;
		        }
	
			}
	        index++ ;
		}	
	}

	public static String[] splitCommentIntoLines(String comment) {
		String lines[] = comment.split("\\r?\\n") ;
		return lines ;
	}

}
