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
		
		String lines[] = DocCommentCleaner.splitCommentIntoLines(comment) ;
		
		try {
		
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, "Parsing the following comment:") ;
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		for(String line: lines) { fLog.debug(ILogLevel.LEVEL_MID, line + "<END>") ; }
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		
		DocCommentCleaner.clean(lines) ;
		
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, "Cleaned the following comment:") ;
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		for(String line: lines) { fLog.debug(ILogLevel.LEVEL_MID, line + "<END>") ; }
		fLog.debug(ILogLevel.LEVEL_MID, "----------------------------------------") ;
		
		parseComment(lines, docTopics) ;
		
		}
		catch(Exception e) {
			fLog.error("Exception while parsing doc comment",e) ;
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
	
	public int parseComment(String lines[], Set<DocTopic> parsedTopics) {
	
	    int topicCount = 0 ;
	    boolean prevLineBlank = true ;
	    boolean inCodeSection = false ;

//	    my ($type, $scope, $isPlural, $title, $symbol);
//	    #my $package;  # package variable.
//	
	    int index = 0 ;
	    
//	    Scope scope = Scope.NONE ;
//	    String topicType = null ;
	    String title = null ;
//	    boolean isPlural = false ;
	
	    int bodyStart = 0 ;
	    int bodyEnd = 0 ; // Note inclusive
	    
	    Tuple<String,String> tupleKeywordTitle = new Tuple<String,String>(null,null) ;

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
	            	
	            	String body = formatBody(lines, bodyStart, bodyEnd /* , topicType, isPlural */) ;
	            	String summary = "" ;
	            	if(body != null) {
	            		summary = getSummaryFromBody(body) ; 
	            	}
	            	DocTopic newTopic = new DocTopic("todo-name-me",DocItemType.Topic, body, title, summary) ;
	            	
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
	            // FIXME: move pattern out into static... no need to keep recompiling
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

        	String body = formatBody(lines, bodyStart, bodyEnd /* , topicType, isPlural */) ;
        	String summary = "" ;
        	if(body != null) {
        		summary = getSummaryFromBody(body) ; 
        	}
        	DocTopic newTopic = new DocTopic("todo-name-me",DocItemType.Topic, body, title, summary) ;
        	
        	parsedTopics.add(newTopic) ;
        	
        	topicCount++ ;

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
	
	enum Tag { NONE, PARAGRAPH, BULLETLIST, DESCRIPTIONLIST, HEADING, PREFIXCODE, TAGCODE } ;
	
	private static final Map<Tag,String> fTagEnders ;
	
	static {
		fTagEnders = new HashMap<Tag,String>() ;
		fTagEnders.put(Tag.NONE, "") ;
		fTagEnders.put(Tag.PARAGRAPH, "</p>") ;
		fTagEnders.put(Tag.BULLETLIST, "</li></ul>") ;
		fTagEnders.put(Tag.DESCRIPTIONLIST, "</dd></dl>") ;
		fTagEnders.put(Tag.HEADING, "</h>") ;
//		fTagEnders.put(Tag.PREFIXCODE, "</code>") ;
		fTagEnders.put(Tag.PREFIXCODE, "</pre></blockquote>") ;
		fTagEnders.put(Tag.TAGCODE, "</code>") ;
	}
	
	//
	//    Function: FormatBody
	//
	//    Converts the section body to <NDMarkup>.
	//
	//    Parameters:
	//
	//       commentLines - The arrayref of comment lines.
	//       startingIndex  - The starting index of the body to format.
	//       endingIndex   - The ending index of the body to format, *not* inclusive.
	//       type               - The type of the section.  May be undef for headerless comments.
	//       isList              - Whether it's a list topic.
	//
	//    Returns:
	//
	//        The body formatted in <NDMarkup>.
	//
	@SuppressWarnings("unused")
	private String formatBody(String[] lines, int startIndex, int endIndex) {

		Tag topLevelTag = Tag.NONE ; 
		String output = "" ;
		
	    String textBlock = null ;
	    boolean prevLineBlank = true ;

//	    String codeBlock = null ;
//	    int removedCodeSpaces = 0 ;
	    
	    Tuple<String,Integer> codeBlockTuple = new Tuple<String,Integer>("",0) ;
	
	    boolean ignoreListSymbols;

	    int index = startIndex ;
	
	    while (index < endIndex) {
	    	
	    	Pattern codeDesignatorPattern = Pattern.compile("^ *[>:|](.*)$") ;
	    	Matcher codeDesignatorMatcher = codeDesignatorPattern.matcher(lines[index]) ;
	    
	        // If we're in a tagged code section...
	    	//
	        if (topLevelTag == Tag.TAGCODE) {
	        	
//	            if ($commentLines->[$index] =~ /^ *\( *(?:end|finish|done)(?: +(?:table|code|example|diagram))? *\)$/i)
	        	if(false) 
	                {
//	                $codeBlock =~ s/\n+$//;
//	                $output .= NaturalDocs::NDMarkup->ConvertAmpChars($codeBlock) . '</code>';
//	                $codeBlock = undef;
//	                $topLevelTag = TAG_NONE;
//	                $prevLineBlank = undef;
	                }
	            else
	            {
	                AddToCodeBlock(lines[index], codeBlockTuple) ;
	            };
	        	
            }
	
	        else if (codeDesignatorMatcher.matches()) {
	        
	        	String code = codeDesignatorMatcher.group(1) ;

	            if (topLevelTag == Tag.PREFIXCODE) {
	                 AddToCodeBlock(code, codeBlockTuple) ;
	            }
	            else // $topLevelTag != TAG_PREFIXCODE
	                {
	            	if(textBlock != null) {
	            		output += richFormatTextBlock(textBlock) + fTagEnders.get(topLevelTag) ;
	            		textBlock = null ;
	            	} 
	                topLevelTag = Tag.PREFIXCODE;
//	                output += "<code type=\"anonymous\">" ;
	                output += "<blockquote><pre>" ;
	                AddToCodeBlock(code, codeBlockTuple) ;
	                    
	            }
            }

	        // If we're not in either code style...
	        //
	        else {
	        
	            // Strip any leading whitespace.
	        	//
	            lines[index] = lines[index].replaceFirst("^ +","") ;
	            
	            Pattern bulletLinePatter = Pattern.compile("^[-\\*o+] +([^ ].*)$") ; 
	            Matcher bulletLineMatcher = bulletLinePatter.matcher(lines[index]) ;
	
	            // If we were in a prefixed code section...
	            //
	            if (topLevelTag == Tag.PREFIXCODE) {

//	                $codeBlock =~ s/\n+$//;
	            	
	            	output += convertAmpChars(codeBlockTuple.first()) + "</pre></blockquote>" ;
	            	
	                codeBlockTuple.setFirst("") ;
	                codeBlockTuple.setSecond(0) ;
	                topLevelTag = Tag.NONE;
	                prevLineBlank = false ;
	            	
                }
	
	            // If the line is blank...
	            //
	            if (lines[index].length() == 0) {
	            	// End a paragraph.  Everything else ignores it for now.
	            	//
	            	if (topLevelTag == Tag.PARAGRAPH)
	            	{
	            		output += richFormatTextBlock(textBlock) + "</p>" ;
	            		textBlock = null ;
	            		topLevelTag = Tag.NONE;
	            	}

	            	prevLineBlank = true ;
	
	            // If the line starts with a bullet...
	            //
	            } else if (bulletLineMatcher.matches() 
	            		&& !bulletLineMatcher.group(1).substring(0, 2).matches("- ")) {
	            	
	                String bulletedText = bulletLineMatcher.group(1) ;

	                if (textBlock != null) {  
	                	output += richFormatTextBlock(textBlock) ;  
	                } ;

	                if (topLevelTag == Tag.BULLETLIST) {
	                	output += "</li><li>" ;
	                } else {
	                	output += fTagEnders.get(topLevelTag) + "<ul><li>" ;
	                	topLevelTag = Tag.BULLETLIST;
	                }
	
	                textBlock = bulletedText ;
	
	                prevLineBlank = false ;
	            }
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
	            else {
	            	
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
        } else if (codeBlockTuple.first().length() != 0) {
        	codeBlockTuple.setFirst(codeBlockTuple.first().replaceFirst("\\n+$", "")) ;
        	output += convertAmpChars(codeBlockTuple.first()) + "</pre></blockquote>" ;
        }
	
	    return output ;
		
    }
	
	
	//
	//   Function: AddToCodeBlock
	//
	//   Adds a line of text to a code block, handling all the indentation processing required.
	//
	//   Parameters:
	//
	//       line - The line of text to add.
	//       codeBlockRef - A reference to the code block to add it to.
	//       removedSpacesRef - A reference to a variable to hold the number of spaces removed.  It needs to be stored between calls.
	//                                      It will reset itself automatically when the code block codeBlockRef points to is undef.
	//
	
	private void AddToCodeBlock(String line, Tuple<String,Integer> codeBlockTuple) {
		
		Pattern patternLeadingWhiteSpaces = Pattern.compile("^( *)(.*)$") ;
		Matcher matcherLeadingWhiteSpace = patternLeadingWhiteSpaces.matcher(line) ;
		
		String spaces = null ;
		String code = null ;
		
		if(!matcherLeadingWhiteSpace.matches()) {
			// FIXME: report error condition. this should always match
		} else {
			spaces = matcherLeadingWhiteSpace.group(1) ;
			code = matcherLeadingWhiteSpace.group(2) ;
		}
		
		if (codeBlockTuple.first().length()==0) {
			
			if (code.length() != 0) {
				codeBlockTuple.setFirst( codeBlockTuple.first() + code + "\n");
				codeBlockTuple.setSecond(spaces.length()) ;
			}
	        
	    // else ignore leading line breaks.
	    //	
        } else if (code.length() != 0) {
        	
	        // Make sure we have the minimum amount of spaces to the left possible.
        	//
        	if (spaces.length() != codeBlockTuple.second() ) {

        		int spaceDifference = 0 ;
        		if(spaces.length() >= codeBlockTuple.second()) {
        			spaceDifference = spaces.length() - codeBlockTuple.second() ;
        		}
        		String spacesToAdd = "" ;
        		for(int i=0 ; i<spaceDifference ; i++) {
        			spacesToAdd += " " ;
        		}

        		if (spaces.length() > codeBlockTuple.second()) {
        			codeBlockTuple.setFirst( codeBlockTuple.first() + spacesToAdd) ;
        		} else {
        			codeBlockTuple.setFirst( spacesToAdd + codeBlockTuple.first()) ;
        			codeBlockTuple.setSecond(spaces.length()) ;
        		}
        	}
	        codeBlockTuple.setFirst( codeBlockTuple.first() + code + "\n") ;
	        
        } else {
        	codeBlockTuple.setFirst( codeBlockTuple.first() + "\n") ;
        } 
		
    }
	
	//
	//   Function: RichFormatTextBlock
	//
	//   Applies rich <NDMarkup> formatting to a chunk of text.  This includes both amp chars, formatting tags, and link tags.
	//
	//   Parameters:
	//
	//       text - The block of text to format.
	//
	//   Returns:
	//
	//       The formatted text block.
	//
	
	@SuppressWarnings("unused")
	private String richFormatTextBlock(String text) {
		
		String output = "" ;
		
				fLog.debug(ILogLevel.LEVEL_MID,
					"ricFormatTextBlock: begin") ;
				fLog.debug(ILogLevel.LEVEL_MID, "------------------------------------") ;
				fLog.debug(ILogLevel.LEVEL_MID, text) ;
				fLog.debug(ILogLevel.LEVEL_MID, "------------------------------------") ;
		
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
		
		String[] tempTextBlocks = text.split("((?<=[\\*_<>\\x1E\\x1F])|(?=[\\*_<>\\x1E\\x1F]))") ;
	
	    // Since the symbols are considered dividers, empty strings could appear between two in a row or at the beginning/end of the
	    // array.  This could seriously screw up TagType(), so we need to get rid of them.
		//
	    ArrayList<String> textBlocks = new ArrayList<String>() ;

	    for(String block: tempTextBlocks) {
	    	if(block.length() != 0) {
	    		textBlocks.add(block) ;
	    	}
	    }
	    
	    boolean bold = false ;
	    boolean underline = false ;
	    boolean underlineHasWhitespace = false ;

	    int index = 0 ;

	    while (index < textBlocks.size()) {
	    	
	        if (textBlocks.get(index).matches("\\x1E")) {
	    		
	            output += '<';
	            index++;
	
	            while (!textBlocks.get(index).matches("\\x1F")) {
	                output += textBlocks.get(index) ;
	                index++ ;
                } ;
	
	            output += ">" ;

	        } else if (textBlocks.get(index).matches("<") && tagType(textBlocks, index) == TagType.POSSIBLE_OPENING_TAG) {
	        	
	        	Tuple<Integer, Boolean> closingTagTuple = closingTag(textBlocks, index) ;
	
	            if (closingTagTuple.first() != -1) {
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
//	    		
	            } else { // it's not a link.
	                
	                output += "&lt;" ;
	            }

	    	} else if (textBlocks.get(index).matches("\\*")) {
	    		
	    		TagType tagType = tagType(textBlocks, index) ;
	    		
	    		Tuple<Integer,Boolean> closingTagTuple = closingTag(textBlocks, index) ;
	    		
	             if (tagType == TagType.POSSIBLE_OPENING_TAG && closingTagTuple.first() != -1) {
	                // ClosingTag() makes sure tags aren't opened multiple times in a row.
	                bold = true ;
	                output += "<b>" ;
	                }
	             else if (bold && tagType == TagType.POSSIBLE_CLOSING_TAG)
	                {
	                bold = false;
	                output += "</b>";
	                }
	            else {
	                output += "*" ;
	                } ;
	
	    	} else if (textBlocks.get(index).matches("_")) {
	    		
	    		TagType tagType = tagType(textBlocks, index) ;
	    		
	    		Tuple<Integer,Boolean> closingTagTuple = closingTag(textBlocks, index) ;
	
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
	    		 else
	                {
	                output += "_" ;
	                } ;

	    	//  plain text or a > that isn't part of a link
            //
	    	} else {
	            output += convertAmpChars(textBlocks.get(index)) ;
	        } ;
	
	    	
	        index++ ;
        } 
        
	    fLog.debug(ILogLevel.LEVEL_MID, "ricFormatTextBlock: end") ;
	    fLog.debug(ILogLevel.LEVEL_MID, "------------------------------------") ;
	    fLog.debug(ILogLevel.LEVEL_MID, output) ;
	    fLog.debug(ILogLevel.LEVEL_MID, "------------------------------------") ;
	
	    return output ;
	    
    }


	//
	//   Function: TagType
	//
	//   Returns whether the tag is a possible opening or closing tag, or neither.  "Possible" because it doesn't check if an opening tag is
	//   closed or a closing tag is opened, just whether the surrounding characters allow it to be a candidate for a tag.  For example, in
	//   "A _B" the underscore is a possible opening underline tag, but in "A_B" it is not.  Support function for <RichFormatTextBlock()>.
	//
	//   Parameters:
	//
	//       textBlocks  - A reference to an array of text blocks.
	//       index         - The index of the tag.
	//
	//   Returns:
	//
	//       POSSIBLE_OPENING_TAG, POSSIBLE_CLOSING_TAG, or NOT_A_TAG.
	//
	private TagType tagType (ArrayList<String> textBlocks, int index) {

	    // Possible opening tags
		//
	    if ( textBlocks.get(index).matches("^[\\*_<]$") &&

	        // Before it must be whitespace, the beginning of the text, or ({["'-/*_.
	        ( index == 0 || textBlocks.get(index-1).matches(".*[ \\t\\n\\(\\{\\[\"'\\-\\/\\*_]$")) &&
	
	        // Notes for 2.0: Include Spanish upside down ! and ? as well as opening quotes (66) and apostrophes (6).  Look into
	        // Unicode character classes as well.
	
	        // After it must be non-whitespace.
	        ((index + 1 < textBlocks.size()) && !textBlocks.get(index+1).matches("^[ \\t\\n]")) &&

	        // Make sure we don't accept <<, <=, <-, or *= as opening tags.
	        ( !textBlocks.get(index).matches("<") || !textBlocks.get(index+1).matches("^[<=-]" )) &&
	        ( !textBlocks.get(index).matches("\\*") || !textBlocks.get(index+1).matches("^[\\=\\*]")) &&
	
	        // Make sure we don't accept * or _ before it unless it's <.
	        ( textBlocks.get(index).matches("<") || index == 0 || !textBlocks.get(index-1).matches("[\\*\\_]$") ))
	     {
	        return TagType.POSSIBLE_OPENING_TAG ;
	     }
	
	
	    // Possible closing tags
	    //
	    else if ( ( textBlocks.get(index).matches("^[\\*_>]$")) &&

//	            // After it must be whitespace, the end of the text, or )}].,!?"';:-/*_.
//	            ( $index + 1 == scalar @$textBlocks || $textBlocks->[$index+1] =~ /^[ \t\n\)\]\}\.\,\!\?\"\'\;\:\-\/\*\_]/ ||
//	              # Links also get plurals, like <link>s, <linx>es, <link>'s, and <links>'.
//	              ( $textBlocks->[$index] eq '>' && $textBlocks->[$index+1] =~ /^(?:es|s|\')/ ) ) &&
	    		
	    		( index+1 == textBlocks.size() || textBlocks.get(index).matches("^[ \\t\\n\\)\\]\\}\\.\\,\\!\\?\"\'\\;\\:\\-\\/\\*\\_]")) &&

	            // Notes for 2.0: Include closing quotes (99) and apostrophes (9).  Look into Unicode character classes as well.

	            // Before it must be non-whitespace.
	            ( index != 0 && !textBlocks.get(index-1).matches("[ \\t\\n]$")) &&
//	
//	            // Make sure we don't accept >>, ->, or => as closing tags.  >= is already taken care of.
//	            ( $textBlocks->[$index] ne '>' || $textBlocks->[$index-1] !~ /[>=-]$/ ) &&
//	
	            // Make sure we don't accept * or _ after it unless it's >.
	            ( !textBlocks.get(index).matches(">") || !textBlocks.get(index+1).matches("[\\*\\_]$")))
	    {
	        return TagType.POSSIBLE_CLOSING_TAG ;
	    }

	    else
	        {
	        return TagType.NOT_A_TAG ;
	        } 

    } ;


	//
	//   Function: ClosingTag
	//
	//   Returns whether a tag is closed or not, where it's closed if it is, and optionally whether there is any whitespace between the
	//   tags.  Support function for <RichFormatTextBlock()>.
	//
	//   The results of this function are in full context, meaning that if it says a tag is closed, it can be interpreted as that tag in the
	//   final output.  It takes into account any spoiling factors, like there being two opening tags in a row.
	//
	//   Parameters:
	//
	//       textBlocks             - A reference to an array of text blocks.
	//       index                    - The index of the opening tag.
	//       hasWhitespaceRef  - A reference to the variable that will hold whether there is whitespace between the tags or not.  If
	//                                     undef, the function will not check.  If the tag is not closed, the variable will not be changed.
	//
	//   Returns:
	//
	//       If the tag is closed, it returns the index of the closing tag and puts whether there was whitespace between the tags in
	//       hasWhitespaceRef if it was specified.  If the tag is not closed, it returns -1 and doesn't touch the variable pointed to by
	//       hasWhitespaceRef.
    //
    Tuple<Integer, Boolean> closingTag(ArrayList<String> textBlocks, int index) {
    	
    	Tuple<Integer, Boolean> result = new Tuple<Integer, Boolean>(-1,false) ;
    	
    	try {
	
	    boolean hasWhitespace = false ;

	    String closingTag = null ;

	    if (textBlocks.get(index).matches("\\*") || textBlocks.get(index).matches("_"))
	        {  closingTag = textBlocks.get(index) ;  }
	    else if (textBlocks.get(index).matches("\\<"))
	        {  closingTag = "\\>" ;  }
	    else
	        {  
	    	return result ;  
    	} ;
	
	    int beginningIndex = index ;
	    index++ ;
	
	    while (index < textBlocks.size())
	        {
	        if (textBlocks.get(index).matches("\\<") && tagType(textBlocks, index) == TagType.POSSIBLE_OPENING_TAG) {

	            // If we hit a < and we're checking whether a link is closed, it's not.  The first < becomes literal and the second one
	            // becomes the new link opening.
	            if (closingTag.equals("\\>"))
	                {
	                return result ;
	                }
	
	            // If we're not searching for the end of a link, we have to skip the link because formatting tags cannot appear within
	            // them.  That's of course provided it's closed.
	            else
	                {
//	                boolean linkHasWhitespace;
	
//	                int $endIndex = $self->ClosingTag($textBlocks, $index,
//	                                 ($hasWhitespaceRef && !$hasWhitespace ? \$linkHasWhitespace : undef) );
//	                int $endIndex = closingTag(textBlocks, index) ;
	                Tuple<Integer, Boolean> closingTagTuple = closingTag(textBlocks, index) ;
	                
	                int endIndex = closingTagTuple.first() ;
	                boolean linkHasWhitespace = closingTagTuple.second() ; 
	
	                if (endIndex != -1) {
	                    if (linkHasWhitespace)
	                        {  hasWhitespace = true ;  };
	
	                    // index will be incremented again at the end of the loop, which will bring us past the link's >.
	                    index = endIndex;
	                    }
	                }
	            
	        } else if (textBlocks.get(index).equals(closingTag)) {

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

	        	// If there are two opening tags of the same type, the first becomes literal and the next becomes part of a tag.
	        	//
	        	} else if (tagType == TagType.POSSIBLE_OPENING_TAG) {  
	        		return result ;
	        	}
	        	
	        } else if (!result.second()) {
	        	if (textBlocks.get(index).matches("[ \t\n]")) {
	        		result.setSecond(true) ;
	        	}
	        } 

	        index++;
        } ;
        
    	}
    	catch (Exception e){
    		fLog.error("Exception caught looking for closing tag", e) ;
    	}
	
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
	
	
	private String getSummaryFromBody (String body) {
		
		String summary = "" ;

		// Extract the first sentence from the leading paragraph, if any.  We'll tolerate a single header beforehand, but nothing else.
		
		Pattern pattern = Pattern.compile("^(?:<h>[^<]*<\\/h>)?<p>(.*?)(</p>|[\\.!\\?](?:[\\)}' ]|&quot;|&gt;)).*",Pattern.DOTALL) ;
		
		Matcher matcher = pattern.matcher(body) ;

		if (matcher.matches()) {
        	summary = matcher.group(1) ;
        	if ((matcher.group(2) != null) &&  !(matcher.group(2).equals("</p>"))) {  
        		summary += matcher.group(2);  
        	} ;
        }
        	

        return summary ;
    }



}