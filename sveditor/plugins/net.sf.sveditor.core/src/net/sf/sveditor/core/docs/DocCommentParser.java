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
 * This class is largely a Java port of the natural docs native format 
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

package net.sf.sveditor.core.docs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.docs.model.DocItemType;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class DocCommentParser implements IDocCommentParser {
	
	private static Pattern fIsDocCommentPattern ;
	
	private LogHandle fLog ;
	
	// FIXME: this should be replaced by something along the lines of the Topic interface from ND
	
	static {
		fIsDocCommentPattern = Pattern.compile(
						"("
					+		"class"
					+   	"|task"
					+   	"|function"
					+   ")\\s*:\\s*(\\w+)",
			Pattern.CASE_INSENSITIVE) ;
	}
	
	public DocCommentParser() {
		fLog = LogFactory.getLogHandle("DocCommentParser") ;
	}

	public String isDocComment(String comment) {
		Matcher matcher = fIsDocCommentPattern.matcher(comment) ;
		if(matcher.find()) {
			return matcher.group(2) ;
		} else {
			return null ;
		}
	}

	public void parse(String comment, Set<DocTopic> docTopics) {
		
		String lines[] = comment.split("\\r?\\n") ;
		
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, "Parsing the following comment:") ;
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		for(String line: lines) { fLog.debug(ILogLevel.LEVEL_MID, line + "<END>") ; }
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		
		cleanComment(lines) ;
		
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, "Cleaned the following comment:") ;
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		for(String line: lines) { fLog.debug(ILogLevel.LEVEL_MID, line + "<END>") ; }
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		
		parseComment(lines, docTopics) ;
		
//	        {  return NaturalDocs::Parser::Native->ParseComment($commentLines, $isJavaDoc, $lineNumber, \@parsedFile);  }
		
	}

//	#
//	#   Function: CleanComment
//	#
//	#   Removes any extraneous formatting and whitespace from the comment.  Eliminates comment boxes, horizontal lines, trailing
//	#   whitespace from lines, and expands all tab characters.  It keeps leading whitespace, though, since it may be needed for
//	#   example code, and blank lines, since the original line numbers are needed.
//	#
	
	private enum Uniformity { DONT_KNOW, IS_UNIFORM, IS_UNIFORM_IF_AT_END, IS_NOT_UNIFORM } ;
	
	private void cleanComment(String[] lines) {
//	
//	    use constant DONT_KNOW => 0;
//	    use constant IS_UNIFORM => 1;
//	    use constant IS_UNIFORM_IF_AT_END => 2;
//	    use constant IS_NOT_UNIFORM => 3;
//	
//	    my $leftSide = DONT_KNOW;
//	    my $rightSide = DONT_KNOW;
//	    my $leftSideChar;
//	    my $rightSideChar;
		
		Uniformity leftSide = Uniformity.DONT_KNOW ;
		Uniformity rightSide = Uniformity.DONT_KNOW ;
		
//	
//	    my $index = 0;
//	    my $tabLength = NaturalDocs::Settings->TabLength();
		
		String tabExpansion = "   " ;
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
			
			lines[index] = lines[index].replaceAll("\\n", tabExpansion) ;

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



//	###############################################################################
//	#
//	#   Package: NaturalDocs::Parser::Native
//	#
//	###############################################################################
//	#
//	#   A package that converts comments from Natural Docs' native format into <NaturalDocs::Parser::ParsedTopic> objects.
//	#   Unlike most second-level packages, these are packages and not object classes.
//	#
//	###############################################################################
//	
//	# This file is part of Natural Docs, which is Copyright  2003-2010 Greg Valure
//	# Natural Docs is licensed under version 3 of the GNU Affero General Public License (AGPL)
//	# Refer to License.txt for the complete details
//	
//	
//	use strict;
//	use integer;
//	
//	package NaturalDocs::Parser::Native;
//	
//	
//	###############################################################################
//	# Group: Variables
//	
//	
//	# Return values of TagType().  Not documented here.
//	use constant POSSIBLE_OPENING_TAG => 1;
//	use constant POSSIBLE_CLOSING_TAG => 2;
//	use constant NOT_A_TAG => 3;
	
	
	enum TagType { POSSIBLE_OPENING_TAG,
				   POSSIBLE_CLOSING_TAG,
				   NOT_A_TAG } ;
//	
//	
//	#
//	#   var: package
//	#
//	#   A <SymbolString> representing the package normal topics will be a part of at the current point in the file.  This is a package variable
//	#   because it needs to be reserved between function calls.
//	#
//	my $package;
//	
//	#
//	#   hash: functionListIgnoredHeadings
//	#
//	#   An existence hash of all the headings that prevent the parser from creating function list symbols.  Whenever one of
//	#   these headings are used in a function list topic, symbols are not created from definition lists until the next heading.  The keys
//	#   are in all lowercase.
//	#
//	my %functionListIgnoredHeadings = ( 'parameters' => 1,
//	                                                       'parameter' => 1,
//	                                                       'params' => 1,
//	                                                       'param' => 1,
//	                                                       'arguments' => 1,
//	                                                       'argument' => 1,
//	                                                       'args' => 1,
//	                                                       'arg' => 1 );
//	
//	
//	###############################################################################
//	# Group: Interface Functions
//	


//#
//#   Constants: ScopeType
//#
//#   The possible values for <Scope()>.
//#
//#   SCOPE_NORMAL - The topic stays in the current scope without affecting it.
//#   SCOPE_START - The topic starts a scope.
//#   SCOPE_END - The topic ends a scope, returning it to global.
//#   SCOPE_ALWAYS_GLOBAL - The topic is always global, but it doesn't affect the current scope.
//#
//use constant SCOPE_NORMAL => 1;
//use constant SCOPE_START => 2;
//use constant SCOPE_END => 3;
//use constant SCOPE_ALWAYS_GLOBAL => 4;

//	#
//	sub ParseComment #(commentLines, isJavaDoc, lineNumber, parsedTopics)
//	    {
//	    my ($self, $commentLines, $isJavaDoc, $lineNumber, $parsedTopics) = @_;
//	
	
//	private enum Scope { NONE, NORMAL, START, END, ALWAYS_GLOBAL } ;
	
	private int parseComment(String lines[], Set<DocTopic> parsedTopics) {
	
	    int topicCount = 0 ;
	    boolean prevLineBlank = true ;
	    boolean inCodeSection = false ;

//	    my ($type, $scope, $isPlural, $title, $symbol);
//	    #my $package;  # package variable.
//	    my ($newKeyword, $newTitle);
//	
	    int index = 0 ;
	    
//	    Scope scope = Scope.NONE ;
//	    String topicType = null ;
	    String title = null ;
//	    boolean isPlural = false ;
	
	    int bodyStart = 0 ;
	    int bodyEnd = 0 ; // Note inclusive
	    
	    Tuple<String,String> tupleKeywordTitle = new Tuple<String,String>(null,null) ;

//	    while ($index < scalar @$commentLines)
	    
	    while(index < lines.length ) {
	    
	        // Everything but leading whitespace was removed beforehand.
	    	
	    	// FIXME: move out into a static. No need to recompile the pattern each comment
        	Pattern codeSectionEnd = Pattern.compile("^ *\\( *(?:end|finish|done)(?: +(?:table|code|example|diagram))? *\\)$", Pattern.CASE_INSENSITIVE ) ;

	        if (inCodeSection) {
	            if (codeSectionEnd.matcher(lines[index]).matches()) {  inCodeSection = false ;  }
	
	            prevLineBlank = false ;
	            bodyEnd++ ;
            }
	
	        // If the line is empty...
	        //
	        else if(lines[index].length() == 0) {
	            prevLineBlank = true ;
	            if (topicCount != 0) {  bodyEnd++;  }
            }
	
	        // If the line has a recognized header and the previous line is blank...
//	        else if (prevLineBlank && (($newKeyword, $newTitle) = $self->ParseHeaderLine($commentLines->[$index])) )
	        
	        else if(prevLineBlank && parseHeaderLine(tupleKeywordTitle, lines[index]))
	            {
	        	
	            // Process the previous one, if any.
	
	            if (topicCount != 0) {
	            	
	            	// FIXME: not sure if we need to care about scopes since we have the AST and preproc structures 
	            	
//	                if (scope == Scope.START || scope == Scope.END)
//	                    {  $package = undef;  };
//	
//	                my $body = $self->FormatBody($commentLines, $bodyStart, $bodyEnd, $type, $isPlural);
//	                my $newTopic = $self->MakeParsedTopic($type, $title, $package, $body, $lineNumber + $bodyStart - 1, $isPlural);
//	                push @$parsedTopics, $newTopic;
	            	
	            	String body = formatBody(lines, bodyStart, bodyEnd /* , topicType, isPlural */) ;
	            	
	            	DocTopic newTopic = new DocTopic("todo-name-me",DocItemType.Topic, body, title) ;
	            	
	            	parsedTopics.add(newTopic) ;
	            	
//	                $package = $newTopic->Package();
	            	
                }
	            
	            String keyword = tupleKeywordTitle.first() ;

	            title = tupleKeywordTitle.second() ;
	            
	            fLog.debug(ILogLevel.LEVEL_MID, 
	            		"Found header line for keyword(" 
	            			+ keyword + ") title("
	            			+ title + ")") ;
	            
	            // FIXME: will want to grab keyword and associate it with topic... or something like that

//	            my $typeInfo;
//	            ($type, $typeInfo, $isPlural) = NaturalDocs::Topics->KeywordInfo($newKeyword);
//	            $scope = $typeInfo->Scope();
//	
	            bodyStart = index + 1 ;
	            bodyEnd = index + 1 ;
	
	            topicCount++;
	
	            prevLineBlank = false ;
	        	
            }
	        // If we're on a normal content line within a topic
	        //
	        else if (topicCount != 0) {
	            prevLineBlank = false ;
	            bodyEnd++ ;
	            // FIXME: move pattern out into static... no need to keep recompiline
	            Pattern patternCodeSectionStart = Pattern.compile("^ *\\( *(?:(?:start|begin)? +)?(?:table|code|example|diagram) *\\)$", Pattern.CASE_INSENSITIVE) ;
	            if(patternCodeSectionStart.matcher(lines[index]).matches()) {
	            	inCodeSection = true ;
	            }
	            	
            }
	
	        index++ ;
        }

	    // Last one, if any.  This is the only one that gets the prototypes.
	    //
	    if (topicCount != 0) {
	    	
//	        if ($scope == ::SCOPE_START() || $scope == ::SCOPE_END())
//	            {  $package = undef;  };
//	
//	        my $body = $self->FormatBody($commentLines, $bodyStart, $bodyEnd, $type, $isPlural);
//	        my $newTopic = $self->MakeParsedTopic($type, $title, $package, $body, $lineNumber + $bodyStart - 1, $isPlural);
//	        push @$parsedTopics, $newTopic;
//	        $topicCount++;
	    	
        	String body = formatBody(lines, bodyStart, bodyEnd /* , topicType, isPlural */) ;
        	
        	DocTopic newTopic = new DocTopic("todo-name-me",DocItemType.Topic, body, title) ;
        	
        	parsedTopics.add(newTopic) ;
        	
        	topicCount++ ;
//	
//	        $package = $newTopic->Package();
        }
	    
	    return topicCount ;
		
    }

	@SuppressWarnings("unused")
	private boolean parseHeaderLine(Tuple<String, String> tupleKeywordTitle, String line) {
		
		// FIXME: make static
		Pattern patternHeaderLine = Pattern.compile("^ *([a-z0-9 ]*[a-z0-9]): +(.*)$",Pattern.CASE_INSENSITIVE) ;
		
		Matcher matcher = patternHeaderLine.matcher(line) ;
		
		if(matcher.matches()) {
			
			String keyWord = matcher.group(1) ;
			String title = matcher.group(2) ;
			
			// FIXME: lookup topic.  for now just assume this is a known topic
	
	        // We need to do it this way because if you do "if (ND:T->KeywordInfo($keyword)" and the last element of the array it
	        // returns is false, the statement is false.  That is really retarded, but there it is.
//	        my ($type, undef, undef) = NaturalDocs::Topics->KeywordInfo($keyword);
	
//	        if ($type) {  
			if(true) {
				tupleKeywordTitle.setFirst(keyWord) ;
				tupleKeywordTitle.setSecond(title) ;
	        	return true ;
        	}
	        else {  
	        	return false ;  
        	}
        }
	    else {  
	    	return false ;  
    	}
		
	}
	
//	
//	
//	#
//	#   Function: ParseHeaderLine
//	#
//	#   If the passed line is a topic header, returns the array ( keyword, title ).  Otherwise returns an empty array.
//	#
//	sub ParseHeaderLine #(line)
//	    {
//	    my ($self, $line) = @_;
//	
//	    if ($line =~ /^ *([a-z0-9 ]*[a-z0-9]): +(.*)$/i)
//	        {
//	        my ($keyword, $title) = ($1, $2);
//	
//	        # We need to do it this way because if you do "if (ND:T->KeywordInfo($keyword)" and the last element of the array it
//	        # returns is false, the statement is false.  That is really retarded, but there it is.
//	        my ($type, undef, undef) = NaturalDocs::Topics->KeywordInfo($keyword);
//	
//	        if ($type)
//	            {  return ($keyword, $title);  }
//	        else
//	            {  return ( );  };
//	        }
//	    else
//	        {  return ( );  };
//	    };
//	
//	
//	
//	###############################################################################
//	# Group: Support Functions
//	
//	
//	#
//	#   Function: MakeParsedTopic
//	#
//	#   Creates a <NaturalDocs::Parser::ParsedTopic> object for the passed parameters.  Scope is gotten from
//	#   the package variable <package> instead of from the parameters.  The summary is generated from the body.
//	#
//	#   Parameters:
//	#
//	#       type         - The <TopicType>.  May be undef for headerless topics.
//	#       title          - The title of the topic.  May be undef for headerless topics.
//	#       package    - The package <SymbolString> the topic appears in.
//	#       body        - The topic's body in <NDMarkup>.
//	#       lineNumber - The topic's line number.
//	#       isList         - Whether the topic is a list.
//	#
//	#   Returns:
//	#
//	#       The <NaturalDocs::Parser::ParsedTopic> object.
//	#
//	sub MakeParsedTopic #(type, title, package, body, lineNumber, isList)
//	    {
//	    my ($self, $type, $title, $package, $body, $lineNumber, $isList) = @_;
//	
//	    my $summary;
//	
//	    if (defined $body)
//	        {  $summary = NaturalDocs::Parser->GetSummaryFromBody($body);  };
//	
//	    return NaturalDocs::Parser::ParsedTopic->New($type, $title, $package, undef, undef, $summary,
//	                                                                         $body, $lineNumber, $isList);
//	    };
//	
//	
//	#
//	#    Function: FormatBody
//	#
//	#    Converts the section body to <NDMarkup>.
//	#
//	#    Parameters:
//	#
//	#       commentLines - The arrayref of comment lines.
//	#       startingIndex  - The starting index of the body to format.
//	#       endingIndex   - The ending index of the body to format, *not* inclusive.
//	#       type               - The type of the section.  May be undef for headerless comments.
//	#       isList              - Whether it's a list topic.
//	#
//	#    Returns:
//	#
//	#        The body formatted in <NDMarkup>.
//	#
//	sub FormatBody #(commentLines, startingIndex, endingIndex, type, isList)
//	    {
//	    my ($self, $commentLines, $startingIndex, $endingIndex, $type, $isList) = @_;
	
//	    use constant TAG_NONE => 1;
//	    use constant TAG_PARAGRAPH => 2;
//	    use constant TAG_BULLETLIST => 3;
//	    use constant TAG_DESCRIPTIONLIST => 4;
//	    use constant TAG_HEADING => 5;
//	    use constant TAG_PREFIXCODE => 6;
//	    use constant TAG_TAGCODE => 7;
//	
//	    my %tagEnders = ( TAG_NONE() => '',
//	                                 TAG_PARAGRAPH() => '</p>',
//	                                 TAG_BULLETLIST() => '</li></ul>',
//	                                 TAG_DESCRIPTIONLIST() => '</dd></dl>',
//	                                 TAG_HEADING() => '</h>',
//	                                 TAG_PREFIXCODE() => '</code>',
//	                                 TAG_TAGCODE() => '</code>' );
	
	enum Tag { NONE, PARAGRAPH, BULLETLIST, DESCRIPTIONLIST, HEADING, PREFIXCODE, TAGCODE } ;
	
	private static final Map<Tag,String> fTagEnders ;
	
	static {
		fTagEnders = new HashMap<Tag,String>() ;
		fTagEnders.put(Tag.NONE, "") ;
		fTagEnders.put(Tag.PARAGRAPH, "</p>") ;
		fTagEnders.put(Tag.BULLETLIST, "</li></ul>") ;
		fTagEnders.put(Tag.DESCRIPTIONLIST, "</dd></dl>") ;
		fTagEnders.put(Tag.HEADING, "</h>") ;
		fTagEnders.put(Tag.PREFIXCODE, "</code>") ;
		fTagEnders.put(Tag.TAGCODE, "</code>") ;
	}
	
	private String formatBody(String[] lines, int startIndex, int endIndex) {

		Tag topLevelTag = Tag.NONE ; 
		String output = "" ;
		
	    String textBlock = null ;
	    boolean prevLineBlank = true ;

	    String codeBlock = null ;
	    String removedCodeSpaces ;
	
	    boolean ignoreListSymbols;

	    int index = startIndex ;
	
	    while (index < endIndex) {
	    	
	    
	        // If we're in a tagged code section...
	    	//
	        if (topLevelTag == Tag.TAGCODE) {
	        	
//	            if ($commentLines->[$index] =~ /^ *\( *(?:end|finish|done)(?: +(?:table|code|example|diagram))? *\)$/i)
//	                {
//	                $codeBlock =~ s/\n+$//;
//	                $output .= NaturalDocs::NDMarkup->ConvertAmpChars($codeBlock) . '</code>';
//	                $codeBlock = undef;
//	                $topLevelTag = TAG_NONE;
//	                $prevLineBlank = undef;
//	                }
//	            else
//	                {
//	                $self->AddToCodeBlock($commentLines->[$index], \$codeBlock, \$removedCodeSpaces);
//	                };
	        	
            }
	
//	        # If the line starts with a code designator...
//	        elsif ($commentLines->[$index] =~ /^ *[>:|](.*)$/)
//	            {
	        
	        else if (lines[index].matches("^ *[>:|](.*)$")) {
	        
//	            my $code = $1;
//	
//	            if ($topLevelTag == TAG_PREFIXCODE)
//	                {
//	                $self->AddToCodeBlock($code, \$codeBlock, \$removedCodeSpaces);
//	                }
//	            else # $topLevelTag != TAG_PREFIXCODE
//	                {
//	                if (defined $textBlock)
//	                    {
//	                    $output .= $self->RichFormatTextBlock($textBlock) . $tagEnders{$topLevelTag};
//	                    $textBlock = undef;
//	                    };
//	
//	                $topLevelTag = TAG_PREFIXCODE;
//	                $output .= '<code type="anonymous">';
//	                $self->AddToCodeBlock($code, \$codeBlock, \$removedCodeSpaces);
//	                };
            }

	        // If we're not in either code style...
	        //
	        else {
	        
	            // Strip any leading whitespace.
	        	//
	            lines[index] = lines[index].replaceFirst("^ +","") ;
	
	            // If we were in a prefixed code section...
	            if (topLevelTag == Tag.PREFIXCODE) {

//	                $codeBlock =~ s/\n+$//;
//	                $output .= NaturalDocs::NDMarkup->ConvertAmpChars($codeBlock) . '</code>';
	            	
	                codeBlock = null ;
	                topLevelTag = Tag.NONE;
	                prevLineBlank = false ;
	            	
                }
	
	            // If the line is blank...
	            //
	            if (lines[index].length() == 0) 
	                {
	                // End a paragraph.  Everything else ignores it for now.
	            	//
	                if (topLevelTag == Tag.PARAGRAPH)
	                    {
	                    output += richFormatTextBlock(textBlock) + "</p>" ;
	                    textBlock = null ;
	                    topLevelTag = Tag.NONE;
	                    }
	
	                prevLineBlank = true ;
	                }
//	
//	            # If the line starts with a bullet...
//	            elsif ($commentLines->[$index] =~ /^[-\*o+] +([^ ].*)$/ &&
//	                    substr($1, 0, 2) ne '- ')  # Make sure "o - Something" is a definition, not a bullet.
//	                {
//	                my $bulletedText = $1;
//	
//	                if (defined $textBlock)
//	                    {  $output .= $self->RichFormatTextBlock($textBlock);  };
//	
//	                if ($topLevelTag == TAG_BULLETLIST)
//	                    {
//	                    $output .= '</li><li>';
//	                    }
//	                else #($topLevelTag != TAG_BULLETLIST)
//	                    {
//	                    $output .= $tagEnders{$topLevelTag} . '<ul><li>';
//	                    $topLevelTag = TAG_BULLETLIST;
//	                    };
//	
//	                $textBlock = $bulletedText;
//	
//	                $prevLineBlank = undef;
//	                }
//	
//	            # If the line looks like a description list entry...
//	            elsif ($commentLines->[$index] =~ /^(.+?) +- +([^ ].*)$/ && $topLevelTag != TAG_PARAGRAPH)
//	                {
//	                my $entry = $1;
//	                my $description = $2;
//	
//	                if (defined $textBlock)
//	                    {  $output .= $self->RichFormatTextBlock($textBlock);  };
//	
//	                if ($topLevelTag == TAG_DESCRIPTIONLIST)
//	                    {
//	                    $output .= '</dd>';
//	                    }
//	                else #($topLevelTag != TAG_DESCRIPTIONLIST)
//	                    {
//	                    $output .= $tagEnders{$topLevelTag} . '<dl>';
//	                    $topLevelTag = TAG_DESCRIPTIONLIST;
//	                    };
//	
//	                if (($isList && !$ignoreListSymbols) || $type eq ::TOPIC_ENUMERATION())
//	                    {
//	                    $output .= '<ds>' . NaturalDocs::NDMarkup->ConvertAmpChars($entry) . '</ds><dd>';
//	                    }
//	                else
//	                    {
//	                    $output .= '<de>' . NaturalDocs::NDMarkup->ConvertAmpChars($entry) . '</de><dd>';
//	                    };
//	
//	                $textBlock = $description;
//	
//	                $prevLineBlank = undef;
//	                }
//	
//	            # If the line could be a header...
//	            elsif ($prevLineBlank && $commentLines->[$index] =~ /^(.*)([^ ]):$/)
//	                {
//	                my $headerText = $1 . $2;
//	
//	                if (defined $textBlock)
//	                    {
//	                    $output .= $self->RichFormatTextBlock($textBlock);
//	                    $textBlock = undef;
//	                    }
//	
//	                $output .= $tagEnders{$topLevelTag};
//	                $topLevelTag = TAG_NONE;
//	
//	                $output .= '<h>' . $self->RichFormatTextBlock($headerText) . '</h>';
//	
//	                if ($type eq ::TOPIC_FUNCTION() && $isList)
//	                    {
//	                    $ignoreListSymbols = exists $functionListIgnoredHeadings{lc($headerText)};
//	                    };
//	
//	                $prevLineBlank = undef;
//	                }
//	
//	            # If the line looks like a code tag...
//	            elsif ($commentLines->[$index] =~ /^\( *(?:(?:start|begin)? +)?(table|code|example|diagram) *\)$/i)
//	                {
//					my $codeType = lc($1);
//	
//	                if (defined $textBlock)
//	                    {
//	                    $output .= $self->RichFormatTextBlock($textBlock);
//	                    $textBlock = undef;
//	                    };
//	
//	                if ($codeType eq 'example')
//	                	{  $codeType = 'anonymous';  }
//	                elsif ($codeType eq 'table' || $codeType eq 'diagram')
//	                	{  $codeType = 'text';  }
//	                # else leave it 'code'
//	
//	                $output .= $tagEnders{$topLevelTag} . '<code type="' . $codeType . '">';
//	                $topLevelTag = TAG_TAGCODE;
//	                }
//	
//	            # If the line looks like an inline image...
//	            elsif ($commentLines->[$index] =~ /^(\( *see +)([^\)]+?)( *\))$/i)
//	                {
//	                if (defined $textBlock)
//	                    {
//	                    $output .= $self->RichFormatTextBlock($textBlock);
//	                    $textBlock = undef;
//	                    };
//	
//	                $output .= $tagEnders{$topLevelTag};
//	                $topLevelTag = TAG_NONE;
//	
//	                $output .= '<img mode="inline" target="' . NaturalDocs::NDMarkup->ConvertAmpChars($2) . '" '
//	                                . 'original="' . NaturalDocs::NDMarkup->ConvertAmpChars($1 . $2 . $3) . '">';
//	
//	                $prevLineBlank = undef;
//	                }
//	
	            // If the line isn't any of those, we consider it normal text.
	            //
	            else
	                {
	            	
	                // A blank line followed by normal text ends lists.  We don't handle this when we detect if the line's blank because
	                // we don't want blank lines between list items to break the list.
	            	//
	                if (prevLineBlank && (topLevelTag == Tag.BULLETLIST || topLevelTag == Tag.DESCRIPTIONLIST)) {
	                	
	                    output += richFormatTextBlock(textBlock) + fTagEnders.get(topLevelTag) + "<p>" ;
	
	                    topLevelTag = Tag.PARAGRAPH ;
	                    textBlock = null ;
	                    
                    } else if (topLevelTag == Tag.NONE) {
                    	
	                    output += "<p>";
	                    topLevelTag = Tag.PARAGRAPH ;
	                    // textBlock will already be null
                    }
	            	
	            	if(textBlock != null) { textBlock += " " ; }
	            	else { textBlock = new String() ; }
	            	
	                textBlock += lines[index] ;
	
	                prevLineBlank = false ;
	            	
	                }
	        	
            }
	    	
	        index++ ;
        }
	
	    // Clean up anything left dangling.
	    //
	    if (textBlock != null) {
	        output += richFormatTextBlock(textBlock) + fTagEnders.get(topLevelTag) ;
        } else if (codeBlock != null) {
	        codeBlock.replaceFirst("\n+$","") ;
	        output += convertAmpChars(codeBlock) + "</code>" ;
        }
	
	    return output ;
		
    }
	
//	
//	#
//	#   Function: AddToCodeBlock
//	#
//	#   Adds a line of text to a code block, handling all the indentation processing required.
//	#
//	#   Parameters:
//	#
//	#       line - The line of text to add.
//	#       codeBlockRef - A reference to the code block to add it to.
//	#       removedSpacesRef - A reference to a variable to hold the number of spaces removed.  It needs to be stored between calls.
//	#                                      It will reset itself automatically when the code block codeBlockRef points to is undef.
//	#
//	sub AddToCodeBlock #(line, codeBlockRef, removedSpacesRef)
//	    {
//	    my ($self, $line, $codeBlockRef, $removedSpacesRef) = @_;
//	
//	    $line =~ /^( *)(.*)$/;
//	    my ($spaces, $code) = ($1, $2);
//	
//	    if (!defined $$codeBlockRef)
//	        {
//	        if (length($code))
//	            {
//	            $$codeBlockRef = $code . "\n";
//	            $$removedSpacesRef = length($spaces);
//	            };
//	        # else ignore leading line breaks.
//	        }
//	
//	    elsif (length $code)
//	        {
//	        # Make sure we have the minimum amount of spaces to the left possible.
//	        if (length($spaces) != $$removedSpacesRef)
//	            {
//	            my $spaceDifference = abs( length($spaces) - $$removedSpacesRef );
//	            my $spacesToAdd = ' ' x $spaceDifference;
//	
//	            if (length($spaces) > $$removedSpacesRef)
//	                {
//	                $$codeBlockRef .= $spacesToAdd;
//	                }
//	            else
//	                {
//	                $$codeBlockRef =~ s/^(.)/$spacesToAdd . $1/gme;
//	                $$removedSpacesRef = length($spaces);
//	                };
//	            };
//	
//	        $$codeBlockRef .= $code . "\n";
//	        }
//	
//	    else # (!length $code)
//	        {
//	        $$codeBlockRef .= "\n";
//	        };
//	    };
//	
//	
//	#
//	#   Function: RichFormatTextBlock
//	#
//	#   Applies rich <NDMarkup> formatting to a chunk of text.  This includes both amp chars, formatting tags, and link tags.
//	#
//	#   Parameters:
//	#
//	#       text - The block of text to format.
//	#
//	#   Returns:
//	#
//	#       The formatted text block.
//	#
	
//	sub RichFormatTextBlock #(text)
//	    {
//	    my ($self, $text) = @_;
//	    my $output;
//	
	@SuppressWarnings("unused")
	private String richFormatTextBlock(String text) {
		
		String output = "" ;
		
//	
//	    # First find bare urls, e-mail addresses, and images.  We have to do this before the split because they may contain underscores
//	    # or asterisks.  We have to mark the tags with \x1E and \x1F so they don't get confused with angle brackets from the comment.
//	    # We can't convert the amp chars beforehand because we need lookbehinds in the regexps below and they need to be
//	    # constant length.  Sucks, huh?
//	
//	    $text =~ s{
//	                       # The previous character can't be an alphanumeric or an opening angle bracket.
//	                       (?<!  [a-z0-9<]  )
//	
//	                       # Optional mailto:.  Ignored in output.
//	                       (?:mailto\:)?
//	
//	                       # Begin capture
//	                       (
//	
//	                       # The user portion.  Alphanumeric and - _.  Dots can appear between, but not at the edges or more than
//	                       # one in a row.
//	                       (?:  [a-z0-9\-_]+  \.  )*   [a-z0-9\-_]+
//	
//	                       @
//	
//	                       # The domain.  Alphanumeric and -.  Dots same as above, however, there must be at least two sections
//	                       # and the last one must be two to four alphanumeric characters (.com, .uk, .info, .203 for IP addresses)
//	                       (?:  [a-z0-9\-]+  \.  )+  [a-z]{2,4}
//	
//	                       # End capture.
//	                       )
//	
//	                       # The next character can't be an alphanumeric, which should prevent .abcde from matching the two to
//	                       # four character requirement, or a closing angle bracket.
//	                       (?!  [a-z0-9>]  )
//	
//	                       }
//	
//	                       {"\x1E" . 'email target="' . NaturalDocs::NDMarkup->ConvertAmpChars($1) . '" '
//	                       . 'name="' . NaturalDocs::NDMarkup->ConvertAmpChars($1) . '"' . "\x1F"}igxe;
//	
//	    $text =~ s{
//	                       # The previous character can't be an alphanumeric or an opening angle bracket.
//	                       (?<!  [a-z0-9<]  )
//	
//	                       # Begin capture.
//	                       (
//	
//	                       # URL must start with one of the acceptable protocols.
//	                       (?:http|https|ftp|news|file)\:
//	
//	                       # The acceptable URL characters as far as I know.
//	                       [a-z0-9\-\=\~\@\#\%\&\_\+\/\;\:\?\*\.\,]*
//	
//	                       # The URL characters minus period and comma.  If it ends on them, they're probably intended as
//	                       # punctuation.
//	                       [a-z0-9\-\=\~\@\#\%\&\_\+\/\;\:\?\*]
//	
//	                       # End capture.
//	                       )
//	
//	                       # The next character must not be an acceptable character or a closing angle bracket.  It must also not be a
//						   # dot and then an acceptable character.  These will prevent the URL from ending early just to get a match.
//	                       (?!  \.?[a-z0-9\-\=\~\@\#\%\&\_\+\/\;\:\?\*\>]  )
//	
//	                       }
//	
//	                       {"\x1E" . 'url target="' . NaturalDocs::NDMarkup->ConvertAmpChars($1) . '" '
//	                       . 'name="' . NaturalDocs::NDMarkup->ConvertAmpChars($1) . '"' . "\x1F"}igxe;
//	
//	
//	    # Find image links.  Inline images should already be pulled out by now.
//	
//	    $text =~ s{(\( *see +)([^\)\<\>]+?)( *\))}
//	                      {"\x1E" . 'img mode="link" target="' . NaturalDocs::NDMarkup->ConvertAmpChars($2) . '" '
//	                        . 'original="' . NaturalDocs::NDMarkup->ConvertAmpChars($1 . $2 . $3) . '"' . "\x1F"}gie;
//	
//	
//	
//	    # Split the text from the potential tags.
//	
//	    my @tempTextBlocks = split(/([\*_<>\x1E\x1F])/, $text);
		
		String[] tempTextBlocks = text.split("([\\*_<>\\x1E\\x1F])") ;
		
	
	    // Since the symbols are considered dividers, empty strings could appear between two in a row or at the beginning/end of the
	    // array.  This could seriously screw up TagType(), so we need to get rid of them.
		//
	    ArrayList<String> textBlocks = new ArrayList<String>() ;

///	    while (scalar @tempTextBlocks)
//	        {
//	        my $tempTextBlock = shift @tempTextBlocks;
//	
//	        if (length $tempTextBlock)
//	            {  push @textBlocks, $tempTextBlock;  };
//	        };
	    
	    for(String block: tempTextBlocks) {
	    	if(block.length() != 0) {
	    		textBlocks.add(block) ;
	    	}
	    }
	    
	    boolean bold = false ;
	    boolean underline = false ;
	    boolean underlineHasWhitespace = false ;
//	
	    int index = 0 ;
//	
	    while (index < textBlocks.size()) {
	    	
	    	
//	        if ($textBlocks[$index] eq "\x1E")
	    	if(false) {
	    		
//	            {
//	            $output .= '<';
//	            $index++;
//	
//	            while ($textBlocks[$index] ne "\x1F")
//	                {
//	                $output .= $textBlocks[$index];
//	                $index++;
//	                };
//	
//	            $output .= '>';

	    	}
//	        elsif ($textBlocks[$index] eq '<' && $self->TagType(\@textBlocks, $index) == POSSIBLE_OPENING_TAG)
//	            {
//	            my $endingIndex = $self->ClosingTag(\@textBlocks, $index, undef);
//	
//	            if ($endingIndex != -1)
//	                {
//	                my $linkText;
//	                $index++;
//	
//	                while ($index < $endingIndex)
//	                    {
//	                    $linkText .= $textBlocks[$index];
//	                    $index++;
//	                    };
//	                # Index will be incremented again at the end of the loop.
//	
//	                $linkText = NaturalDocs::NDMarkup->ConvertAmpChars($linkText);
//	
//	                if ($linkText =~ /^(?:mailto\:)?((?:[a-z0-9\-_]+\.)*[a-z0-9\-_]+@(?:[a-z0-9\-]+\.)+[a-z]{2,4})$/i)
//	                    {  $output .= '<email target="' . $1 . '" name="' . $1 . '">';  }
//	                elsif ($linkText =~ /^(.+?) at (?:mailto\:)?((?:[a-z0-9\-_]+\.)*[a-z0-9\-_]+@(?:[a-z0-9\-]+\.)+[a-z]{2,4})$/i)
//	                    {  $output .= '<email target="' . $2 . '" name="' . $1 . '">';  }
//	                elsif ($linkText =~ /^(?:http|https|ftp|news|file)\:/i)
//	                    {  $output .= '<url target="' . $linkText . '" name="' . $linkText . '">';  }
//	                elsif ($linkText =~ /^(.+?) at ((?:http|https|ftp|news|file)\:.+)/i)
//	                    {  $output .= '<url target="' . $2 . '" name="' . $1 . '">';  }
//	                else
//	                    {  $output .= '<link target="' . $linkText . '" name="' . $linkText . '" original="&lt;' . $linkText . '&gt;">';  };
//	                }
//	
//	            else # it's not a link.
//	                {
//	                $output .= '&lt;';
//	                };
//	            }
//	
//	        elsif ($textBlocks[$index] eq '*')
//	            {
//	            my $tagType = $self->TagType(\@textBlocks, $index);
//	
//	            if ($tagType == POSSIBLE_OPENING_TAG && $self->ClosingTag(\@textBlocks, $index, undef) != -1)
//	                {
//	                # ClosingTag() makes sure tags aren't opened multiple times in a row.
//	                $bold = 1;
//	                $output .= '<b>';
//	                }
//	            elsif ($bold && $tagType == POSSIBLE_CLOSING_TAG)
//	                {
//	                $bold = undef;
//	                $output .= '</b>';
//	                }
//	            else
//	                {
//	                $output .= '*';
//	                };
//	            }
//	
	    	else if (textBlocks.get(index).matches("_")) {
	    		
//	            my $tagType = $self->TagType(\@textBlocks, $index);
	    		TagType tagType = tagType(textBlocks, index) ;
	    		
	    		Tuple<Integer,Boolean> closingTagTuple = closingTag(textBlocks, index) ;
	
//	             if (tagType == TagType.POSSIBLE_OPENING_TAG && ClosingTag(textBlocks, index, underlineHasWhitespace) != -1)
	             if (tagType == TagType.POSSIBLE_OPENING_TAG && closingTagTuple.first() != -1)
	                {
	                // ClosingTag() makes sure tags aren't opened multiple times in a row.
	                underline = true ;
	                // underlineHasWhitespace is set by ClosingTag().
	                output += "<u>";
	                }
	             else if (underline && tagType == TagType.POSSIBLE_CLOSING_TAG)
	                {
	                underline = false ;
	                // underlineHasWhitespace will be reset by the next opening underline.
                	output += "</u>";
	                }
	             else if (underline && !underlineHasWhitespace)
	                {
	                // If there's no whitespace between underline tags, all underscores are replaced by spaces so
	                // _some_underlined_text_ becomes <u>some underlined text</u>.  The standard _some underlined text_
	                // will work too.
	                output += " " ;
	                }
	    		if(false) {
	    		} else
	                {
	                output += "_" ;
	                } ;
	            }

	    	//  plain text or a > that isn't part of a link
	        else {
	            output += convertAmpChars(textBlocks.get(index)) ;
	        } ;
	
	    	
	        index++ ;
        } ;
	
	    return output ;
	    
    }

	//	
//	#
//	#   Function: TagType
//	#
//	#   Returns whether the tag is a possible opening or closing tag, or neither.  "Possible" because it doesn't check if an opening tag is
//	#   closed or a closing tag is opened, just whether the surrounding characters allow it to be a candidate for a tag.  For example, in
//	#   "A _B" the underscore is a possible opening underline tag, but in "A_B" it is not.  Support function for <RichFormatTextBlock()>.
//	#
//	#   Parameters:
//	#
//	#       textBlocks  - A reference to an array of text blocks.
//	#       index         - The index of the tag.
//	#
//	#   Returns:
//	#
//	#       POSSIBLE_OPENING_TAG, POSSIBLE_CLOSING_TAG, or NOT_A_TAG.
//	#
	private TagType tagType (ArrayList<String> textBlocks, int index) {

//	    my ($self, $textBlocks, $index) = @_;
//	
//	
	    // Possible opening tags
		//
	    if ( textBlocks.get(index).matches("^[\\*_<]$") &&

	        // Before it must be whitespace, the beginning of the text, or ({["'-/*_.
	        ( index == 0 || textBlocks.get(index-1).matches("[\\ \\t\\n\\(\\{\\[\"'\\-\\/\\*\\_]$")) &&
//	
//	        # Notes for 2.0: Include Spanish upside down ! and ? as well as opening quotes (66) and apostrophes (6).  Look into
//	        # Unicode character classes as well.
//	
	        // After it must be non-whitespace.
	        ((index + 1 < textBlocks.size()) && !textBlocks.get(index+1).matches("^[\\ \\t\\n]")) &&

	        // Make sure we don't accept <<, <=, <-, or *= as opening tags.
	        ( !textBlocks.get(index).matches("<") || !textBlocks.get(index+1).matches("^[<=-]" )) &&
	        ( !textBlocks.get(index).matches("*") || !textBlocks.get(index+1).matches("^[\\=\\*]")) &&
	
	        // Make sure we don't accept * or _ before it unless it's <.
	        ( textBlocks.get(index).matches("<") || index == 0 || !textBlocks.get(index-1).matches("[\\*\\_]$") ))
	     {
	        return TagType.POSSIBLE_OPENING_TAG ;
	     }
	
	
	    // Possible closing tags
	    //
	    else if ( ( textBlocks.get(index).matches("^[\\*_>]$")) &&
//	
//	            # After it must be whitespace, the end of the text, or )}].,!?"';:-/*_.
//	            ( $index + 1 == scalar @$textBlocks || $textBlocks->[$index+1] =~ /^[ \t\n\)\]\}\.\,\!\?\"\'\;\:\-\/\*\_]/ ||
//	              # Links also get plurals, like <link>s, <linx>es, <link>'s, and <links>'.
//	              ( $textBlocks->[$index] eq '>' && $textBlocks->[$index+1] =~ /^(?:es|s|\')/ ) ) &&
//	
//	            # Notes for 2.0: Include closing quotes (99) and apostrophes (9).  Look into Unicode character classes as well.
//	
	            // Before it must be non-whitespace.
	            ( index != 0 && !textBlocks.get(index-1).matches("[ \\t\\n]$")) &&
//	
//	            # Make sure we don't accept >>, ->, or => as closing tags.  >= is already taken care of.
//	            ( $textBlocks->[$index] ne '>' || $textBlocks->[$index-1] !~ /[>=-]$/ ) &&
//	
	            // Make sure we don't accept * or _ after it unless it's >.
	            ( !textBlocks.get(index).matches(">") || !textBlocks.get(index+1).matches("[\\*\\_]$")))
	        {
	        return TagType.POSSIBLE_CLOSING_TAG ;
	        }
//	
	    else
	        {
	        return TagType.NOT_A_TAG ;
	        } 

    } ;


//	#
//	#   Function: ClosingTag
//	#
//	#   Returns whether a tag is closed or not, where it's closed if it is, and optionally whether there is any whitespace between the
//	#   tags.  Support function for <RichFormatTextBlock()>.
//	#
//	#   The results of this function are in full context, meaning that if it says a tag is closed, it can be interpreted as that tag in the
//	#   final output.  It takes into account any spoiling factors, like there being two opening tags in a row.
//	#
//	#   Parameters:
//	#
//	#       textBlocks             - A reference to an array of text blocks.
//	#       index                    - The index of the opening tag.
//	#       hasWhitespaceRef  - A reference to the variable that will hold whether there is whitespace between the tags or not.  If
//	#                                     undef, the function will not check.  If the tag is not closed, the variable will not be changed.
//	#
//	#   Returns:
//	#
//	#       If the tag is closed, it returns the index of the closing tag and puts whether there was whitespace between the tags in
//	#       hasWhitespaceRef if it was specified.  If the tag is not closed, it returns -1 and doesn't touch the variable pointed to by
//	#       hasWhitespaceRef.
//	#
//	sub ClosingTag #(textBlocks, index, hasWhitespace)
//	    {
//	    my ($self, $textBlocks, $index, $hasWhitespaceRef) = @_;
	    
//    private int ClosingTag(ArrayList<String> textBlocks, int index, boolean underlineHasWhitespace) {
    
    Tuple<Integer, Boolean> closingTag(ArrayList<String> textBlocks, int index) {
    	
    	Tuple<Integer, Boolean> result = new Tuple<Integer, Boolean>(-1,false) ;
	
	    boolean hasWhitespace = false ;

	    String closingTag = null ;

	    if (textBlocks.get(index).matches("*") || textBlocks.get(index).matches("_"))
	        {  closingTag = textBlocks.get(index) ;  }
	    else if (textBlocks.get(index).matches("<"))
	        {  closingTag = ">" ;  }
	    else
	        {  
	    	return result ;  
    	} ;
	
	    int beginningIndex = index ;
	    index++ ;
	
	    while (index < textBlocks.size())
	        {
	        if (textBlocks.get(index).matches("<") && tagType(textBlocks, index) == TagType.POSSIBLE_OPENING_TAG) {

	            // If we hit a < and we're checking whether a link is closed, it's not.  The first < becomes literal and the second one
	            // becomes the new link opening.
	            if (closingTag.matches(">"))
	                {
	                return result ;
	                }
//	
//	            # If we're not searching for the end of a link, we have to skip the link because formatting tags cannot appear within
//	            # them.  That's of course provided it's closed.
//	            else
//	                {
//	                my $linkHasWhitespace;
//	
//	                my $endIndex = $self->ClosingTag($textBlocks, $index,
//	                                                                    ($hasWhitespaceRef && !$hasWhitespace ? \$linkHasWhitespace : undef) );
//	
//	                if ($endIndex != -1)
//	                    {
//	                    if ($linkHasWhitespace)
//	                        {  $hasWhitespace = 1;  };
//	
//	                    # index will be incremented again at the end of the loop, which will bring us past the link's >.
//	                    $index = $endIndex;
//	                    };
//	                };
	            }
	
	        else if (textBlocks.get(index).matches(closingTag)) {
	        	
	            TagType tagType = tagType(textBlocks, index) ;
	
	            if (tagType == TagType.POSSIBLE_CLOSING_TAG) {
	            	
	                // There needs to be something between the tags for them to count.
	                if (index == beginningIndex + 1) {  
	                	return result ;
	                }
	                else {
	                	
	                    // Success!
	                	//
	                    result.setFirst(index) ;
	                    result.setSecond(hasWhitespace) ;
	
	                } ;
	            }
	
	            // If there are two opening tags of the same type, the first becomes literal and the next becomes part of a tag.
	            //
	            else if (tagType == TagType.POSSIBLE_OPENING_TAG)
	                {  
	                return result ;
	                }
	            }
	
	        else if (!result.second()) {
	            if (textBlocks.get(index).matches("[ \t\n]")) {
	                 result.setSecond(true) ;
	            }
	        } ;

	        index++;
        } ;
	
	    // Hit the end of the text blocks if we're here.
    	
    	return result ;
    	
    } 

//	###############################################################################
//	#
//	#   Package: NaturalDocs::Parser::ParsedTopic
//	#
//	###############################################################################
//	#
//	#   A class for parsed topics of source files.  Also encompasses some of the <TopicType>-specific behavior.
//	#
//	###############################################################################
//	
//	# This file is part of Natural Docs, which is Copyright  2003-2010 Greg Valure
//	# Natural Docs is licensed under version 3 of the GNU Affero General Public License (AGPL)
//	# Refer to License.txt for the complete details
//	
//	use strict;
//	use integer;
//	
//	package NaturalDocs::Parser::ParsedTopic;
//	
//	
//	###############################################################################
//	# Group: Implementation
//	
//	#
//	#   Constants: Members
//	#
//	#   The object is a blessed arrayref with the following indexes.
//	#
//	#       TYPE           - The <TopicType>.
//	#       TITLE          - The title of the topic.
//	#       PACKAGE    - The package <SymbolString> the topic appears in, or undef if none.
//	#       USING         - An arrayref of additional package <SymbolStrings> available to the topic via "using" statements, or undef if
//	#                           none.
//	#       PROTOTYPE - The prototype, if it exists and is applicable.
//	#       SUMMARY    - The summary, if it exists.
//	#       BODY          - The body of the topic, formatted in <NDMarkup>.  Some topics may not have bodies, and if not, this
//	#                           will be undef.
//	#       LINE_NUMBER  - The line number the topic appears at in the file.
//	#       IS_LIST - Whether the topic is a list.
//	#
//	use NaturalDocs::DefineMembers 'TYPE', 'TITLE', 'PACKAGE', 'USING', 'PROTOTYPE', 'SUMMARY', 'BODY',
//	                                                 'LINE_NUMBER', 'IS_LIST';
//	# DEPENDENCY: New() depends on the order of these constants, and that this class is not inheriting any members.
//	
//	
//	#
//	#   Architecture: Title, Package, and Symbol Behavior
//	#
//	#   Title, package, and symbol behavior is a little awkward so it deserves some explanation.  Basically you set them according to
//	#   certain rules, but you get computed values that try to hide all the different scoping situations.
//	#
//	#   Normal Topics:
//	#
//	#       Set them to the title and package as they appear.  "Function" and "PkgA.PkgB" will return "Function" for the title,
//	#       "PkgA.PkgB" for the package, and "PkgA.PkgB.Function" for the symbol.
//	#
//	#       In the rare case that a title has a separator symbol it's treated as inadvertant, so "A vs. B" in "PkgA.PkgB" still returns just
//	#       "PkgA.PkgB" for the package even though if you got it from the symbol it can be seen as "PkgA.PkgB.A vs".
//	#
//	#   Scope Topics:
//	#
//	#       Set the title normally and leave the package undef.  So "PkgA.PkgB" and undef will return "PkgA.PkgB" for the title as well
//	#       as for the package and symbol.
//	#
//	#       The only time you should set the package is when you have full language support and they only documented the class with
//	#       a partial title.  So if you documented "PkgA.PkgB" with just "PkgB", you want to set the package to "PkgA".  This
//	#       will return "PkgB" as the title for presentation and will return "PkgA.PkgB" for the package and symbol, which is correct.
//	#
//	#   Always Global Topics:
//	#
//	#       Set the title and package normally, do not set the package to undef.  So "Global" and "PkgA.PkgB" will return "Global" as
//	#       the title, "PkgA.PkgB" as the package, and "Global" as the symbol.
//	#
//	#   Um, yeah...:
//	#
//	#       So does this suck?  Yes, yes it does.  But the suckiness is centralized here instead of having to be handled everywhere these
//	#       issues come into play.  Just realize there are a certain set of rules to follow when you *set* these variables, and the results
//	#       you see when you *get* them are computed rather than literal.
//	#
//	
//	
//	###############################################################################
//	# Group: Functions
//	
//	
//	# Function: Type
//	# Returns the <TopicType>.
//	sub Type
//	    {  return $_[0]->[TYPE];  };
//	
//	# Function: SetType
//	# Replaces the <TopicType>.
//	sub SetType #(type)
//	    {  $_[0]->[TYPE] = $_[1];  };
//	
//	# Function: IsList
//	# Returns whether the topic is a list.
//	sub IsList
//	    {  return $_[0]->[IS_LIST];  };
//	
//	# Function: SetIsList
//	# Sets whether the topic is a list.
//	sub SetIsList
//	    {  $_[0]->[IS_LIST] = $_[1];  };
//	
//	# Function: Title
//	# Returns the title of the topic.
//	sub Title
//	    {  return $_[0]->[TITLE];  };
//	
//	# Function: SetTitle
//	# Replaces the topic title.
//	sub SetTitle #(title)
//	    {  $_[0]->[TITLE] = $_[1];  };
//	
//	#
//	#   Function: Symbol
//	#
//	#   Returns the <SymbolString> defined by the topic.  It is fully resolved and does _not_ need to be joined with <Package()>.
//	#
//	#   Type-Specific Behavior:
//	#
//	#       - If the <TopicType> is always global, the symbol will be generated from the title only.
//	#       - Everything else's symbols will be generated from the title and the package passed to <New()>.
//	#
//	sub Symbol
//	    {
//	    my ($self) = @_;
//	
//	    my $titleSymbol = NaturalDocs::SymbolString->FromText($self->[TITLE]);
//	
//	    if (NaturalDocs::Topics->TypeInfo($self->Type())->Scope() == ::SCOPE_ALWAYS_GLOBAL())
//	        {  return $titleSymbol;  }
//	    else
//	        {
//	        return NaturalDocs::SymbolString->Join( $self->[PACKAGE], $titleSymbol );
//	        };
//	    };
//	
//	
//	#
//	#   Function: Package
//	#
//	#   Returns the package <SymbolString> that the topic appears in.
//	#
//	#   Type-Specific Behavior:
//	#
//	#       - If the <TopicType> has scope, the package will be generated from both the title and the package passed to <New()>, not
//	#         just the package.
//	#       - If the <TopicType> is always global, the package will be the one passed to <New()>, even though it isn't part of it's
//	#         <Symbol()>.
//	#       - Everything else's package will be what was passed to <New()>, even if the title has separator symbols in it.
//	#
//	sub Package
//	    {
//	    my ($self) = @_;
//	
//	    # Headerless topics may not have a type yet.
//	    if ($self->Type() && NaturalDocs::Topics->TypeInfo($self->Type())->Scope() == ::SCOPE_START())
//	        {  return $self->Symbol();  }
//	    else
//	        {  return $self->[PACKAGE];  };
//	    };
//	
//	
//	# Function: SetPackage
//	# Replaces the package the topic appears in.  This will behave the same way as the package parameter in <New()>.  Later calls
//	# to <Package()> will still be generated according to its type-specific behavior.
//	sub SetPackage #(package)
//	    {  $_[0]->[PACKAGE] = $_[1];  };
//	
//	# Function: Using
//	# Returns an arrayref of additional scope <SymbolStrings> available to the topic via "using" statements, or undef if none.
//	sub Using
//	    {  return $_[0]->[USING];  };
//	
//	# Function: SetUsing
//	# Replaces the using arrayref of sope <SymbolStrings>.
//	sub SetUsing #(using)
//	    {  $_[0]->[USING] = $_[1];  };
//	
//	# Function: Prototype
//	# Returns the prototype if one is defined.  Will be undef otherwise.
//	sub Prototype
//	    {  return $_[0]->[PROTOTYPE];  };
//	
//	# Function: SetPrototype
//	# Replaces the function or variable prototype.
//	sub SetPrototype #(prototype)
//	    {  $_[0]->[PROTOTYPE] = $_[1];  };
//	
//	# Function: Summary
//	# Returns the topic summary, if it exists, formatted in <NDMarkup>.
//	sub Summary
//	    {  return $_[0]->[SUMMARY];  };
//	
//	# Function: Body
//	# Returns the topic's body, formatted in <NDMarkup>.  May be undef.
//	sub Body
//	    {  return $_[0]->[BODY];  };
//	
//	# Function: SetBody
//	# Replaces the topic's body, formatted in <NDMarkup>.  May be undef.
//	sub SetBody #(body)
//	    {
//	    my ($self, $body) = @_;
//	    $self->[BODY] = $body;
//	    };
//	
//	# Function: LineNumber
//	# Returns the line the topic appears at in the file.
//	sub LineNumber
//	    {  return $_[0]->[LINE_NUMBER];  };
//	
//	
//	1;

	//
	//   Substitutes certain characters with their <NDMarkup> amp chars.
	//
	private String convertAmpChars(String text) {

	    text = text.replaceAll("&","&amp;") ;
	    text = text.replaceAll("<","&lt;") ;
	    text = text.replaceAll(">","&gt;") ;
	    text = text.replaceAll("\"","&quot;") ;
	
	    return text ;
		
    }
	
	//
	//   Replaces <NDMarkup> amp chars with their original symbols.
	//
	private String restoreAmpChars(String text) {
	
	    text = text.replaceAll("&quot;","\"") ;
	    text = text.replaceAll("&gt;",">") ;
	    text = text.replaceAll("&lt;","<") ;
	    text = text.replaceAll("&amp;","&") ;

	    return text ;
		
    }

}