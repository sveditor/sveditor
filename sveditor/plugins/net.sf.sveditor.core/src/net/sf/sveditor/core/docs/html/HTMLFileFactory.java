/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs.html;

import java.io.File;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.model.DocFile;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.docs.model.SymbolTableEntry;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class HTMLFileFactory {
	
	private DocGenConfig cfg ;
	private DocModel model ;
	private LogHandle fLog ;
	
	private final static Pattern patternLink = Pattern.compile("\\<link target=\"([^\"]*)\" name=\"([^\"]*)\" original=\"([^\"]*)\"\\>") ;
	
	public HTMLFileFactory(DocGenConfig cfg, DocModel model) {
		this.cfg = cfg ;
		this.model = model ;
		fLog = LogFactory.getLogHandle("DocModelFactory") ;
	}
	
	public static String getRelPathToHTML(String path) {
		String res = "" ;
		File filePath = new File(path) ;
		int numParents=0 ;
		while(filePath.getParentFile() != null) {
			numParents++ ;
			filePath = filePath.getParentFile() ;  
		}
		for(int i=0 ; i<numParents ; i++) {
			res += "../" ;
		}
		return res ;
	}
	
	public String build(DocFile docFile) {
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart(getRelPathToHTML(docFile.getTitle()),docFile.getPageTitle()) ;
		res += HTMLUtils.genBodyBegin("ContentPage") ;
		res += HTMLUtils.genContentBegin() ;
		res += genContent(docFile) ;
		res += HTMLUtils.genContentEnd() ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu(
					cfg, 
					getRelPathToHTML(docFile.getTitle()),
					docFile.getPageTitle(),
					model.getDocTopics().getAllTopicTypes()) ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genSummaryStart(DocFile docFile, DocTopic docItem) {
		String result = "" ;
//		result += docItem.getSummary() ;
		result += convertNDMarkupToHTML(docFile, docItem, docItem.getBody()) ;
		return result ;
	}

	private String genMemberDetail(DocFile docFile, DocTopic docTopic) {
		String res = "" ;
		for(DocTopic child: docTopic.getChildren()) {
			res += genDetails(docFile, docTopic, child) ;
		}
		return res ;
	}

	private String genSTRMain(DocFile docFile, DocTopic topic) {
		String res = "" ;
		if(topic.getTopic().equals("section")) {
			res += 
			 "<tr class=SMain>"
		   + "<td colspan=\"2\" class=SEntry><a href=\"#" 
					 + topic.getQualifiedName()
					 + "\">" + topic.getTitle() + "</a>"
					 + "</td>"
		   + "</tr>" ;
		} else {
			res +=
			  "<tr class=\"SMain\">"
				   + "<td class=SIcon>"
							 + "<img src=" + getRelPathToHTML(topic.getDocFile().getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
							 + "</td>"
			+ "<td class=SEntry><a href=\"#" +topic.getTitle()+ "\" >" +topic.getTitle()+ "</a></td>" 
			+ "<td class=SDescription>" ;
		
			res += topic.getSummary() ;
//			res += convertNDMarkupToHTML(docFile, topic, topic.getBody()) ;
			res += "</tr>" ;
		}
		return res ;
	}	
	
	private String genTopicStart(DocTopic contentItem) {
		String res = 
				"<div class=\""
				  + HTMLUtils.genCSSClassForTopic(contentItem.getTopic()) 
				+"\">" ;
		return res ;
	}
	private String genClassEnd() {
		String res = 
				"</div>" ;
		return res ;
	}
	
	private String genContent(DocFile docFile) {
		String res = "" ;
		if(docFile.getChildren().size() > 1) {
			res += genFileSummary(docFile) ;
		}
		for(DocTopic contentItem: docFile.getChildren()) {
			if(!contentItem.getTopic().equals("section")) {
				res += genContent(docFile, contentItem) ;
			}
		}
		return res ;
	}
	
	private String genContent(DocFile docFile, DocTopic contentItem) {

		String res = "" ;
		res += genTopicStart(contentItem) ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(contentItem.getTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += genSummaryStart(docFile, contentItem) ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		res += genSTRMain(docFile,contentItem) ;
		res += genSummaryMembers(docFile, contentItem) ;
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		res += genClassEnd() ;
		res += genMemberDetail(docFile, contentItem) ;		
		return res ;		
	}

	private String genFileSummary(DocFile docFile) {
		String res = "" ;
		res += genSummaryStart(docFile, docFile) ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(docFile.getPageTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		for(DocTopic docItem: docFile.getChildren()) {
			res += genSTRMain(docFile,docItem) ;
			res += genSummaryMembers(docFile, docItem) ;
		}
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		return res ;
	}

	private String genSummaryMembers(DocFile docFile, DocTopic docTopic) {
		String res = "" ;
		boolean marked = false ;
		for(DocTopic child: docTopic.getChildren()) {
			res += genSummaryForMemember(docFile, docTopic, child, marked) ;
			marked = !marked ;
		}
		return res ;
	}
	
	private String genSummaryForMemember(DocFile docFile, DocTopic parent, DocTopic topic, boolean marked) {
		String res = "" ;
		if(topic.getTopic().equals("group")) {
			res += 
			 "<tr class=\"" + HTMLUtils.genCSSClassForTopicInSummary(topic.getTopic()) ;
			if(marked) {
				res += " SMarked" ;
			}
			res += " SIndent2\">" 
		   + "<td class=SIcon>"
//					 + "<img src=" + getRelPathToHTML(docFile.getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
					 + "</td>"
		   + "<td colspan=2 class=SEntry><a href=\"#" 
					 + topic.getQualifiedName()
					 + "\">" + topic.getTitle() + "</a>"
					 + "</td>"
//		   + "<td class=SDescription>"
//					 + topic.getSummary()
//					 + "</td>"
		   + "</tr>" ;
		} else {
			res += 
			 "<tr class=\"" + HTMLUtils.genCSSClassForTopicInSummary(topic.getTopic()) ;
			if(marked) {
				res += " SMarked" ;
			}
			res += " SIndent3\">" 
		   + "<td class=SIcon>"
					 + "<img src=" + getRelPathToHTML(docFile.getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
					 + "</td>"
		   + "<td class=SEntry>"
//	   				+ "<img src=" + getRelPathToHTML(docFile.getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
		   			+"<a href=\"#" 
		   				+ topic.getQualifiedName()
		   				+ "\">" + topic.getTitle() + "</a>"
				 + "</td>"
		   + "<td class=SDescription>"
					 + topic.getSummary()
					 + "</td>"
		   + "</tr>" ;
		}
		return res ;
	}

	private String genDetails(DocFile docFile, DocTopic parent, DocTopic child) {
		String res =
				  "<div class=" + HTMLUtils.genCSSClassForTopic(child.getTopic()) + ">" 
				    + "<div class=CTopic>" 
					    + "<h3 class=CTitle>"
							+ "<a name=\"" 
								+ child.getQualifiedName()
						    + "\"></a>"
					    + child.getTitle()
					    + "</h3>"
					    + "<div class=CBody>" ; 
//		res += child.getBody() ;
		res += convertNDMarkupToHTML(docFile, child, child.getBody()) ;
		res += 
					      "</div>"
				    + "</div>"
			    + "</div>" ;
		return res ;
	}
	
//#
//#   Function: NDMarkupToHTML
//#
//#   Converts a block of <NDMarkup> to HTML.
//#
//#   Parameters:
//#
//#       sourceFile - The source <FileName> the <NDMarkup> appears in.
//#       text    - The <NDMarkup> text to convert.
//#       symbol - The topic <SymbolString> the <NDMarkup> appears in.
//#       package  - The package <SymbolString> the <NDMarkup> appears in.
//#       type - The <TopicType> the <NDMarkup> appears in.
//#       using - An arrayref of scope <SymbolStrings> the <NDMarkup> also has access to, or undef if none.
//#       style - Set to one of the <NDMarkupToHTML Styles> or leave undef for general.
//#
//#   Returns:
//#
//#       The text in HTML.
//#
//sub NDMarkupToHTML #(sourceFile, text, symbol, package, type, using, style)
//    {
	
	@SuppressWarnings("unused")
	private String convertNDMarkupToHTML(DocFile docFile, DocTopic docTopic, String markup) {
		String output = "" ;
		
//    my ($self, $sourceFile, $text, $symbol, $package, $type, $using, $style) = @_;
//
//    my $dlSymbolBehavior;
//
//    if ($type eq ::TOPIC_ENUMERATION())
//        {  $dlSymbolBehavior = NaturalDocs::Languages->LanguageOf($sourceFile)->EnumValues();  }
//   elsif (NaturalDocs::Topics->TypeInfo($type)->Scope() == ::SCOPE_ALWAYS_GLOBAL())
//        {  $dlSymbolBehavior = ::ENUM_GLOBAL();  }
//    else
//        {  $dlSymbolBehavior = ::ENUM_UNDER_PARENT();  };
//
//    my $output;
//    my $inCode;
//
//    my @splitText = split(/(<\/?code(?: type="[^"]+")?>)/, $text);
		
		String splitText[] = markup.split("(</?code(?: type=\"[^\"]+\")?>)") ;
		
		int index=0 ;
		
		while(index < splitText.length) {
		
			String text = splitText[index] ;

//        	if ($text =~ /<code type="([^"]+)">/)
			if(false) {
				
//            my $codeType = $1;
//
//            my $highlight = ( ($codeType eq "code" && NaturalDocs::Settings->HighlightCode()) ||
//            						  ($codeType eq "anonymous" && NaturalDocs::Settings->HighlightAnonymous()) );
//
//            $output .= '<blockquote><pre' . ($highlight ? ' class="prettyprint"' : '') . '>';
//            $inCode = 1;
				
//        	elsif ($text eq '</code>')
			} else if(false) {
			
//            $output .= '</pre></blockquote>';
//            $inCode = undef;
				
//        	elsif ($inCode)
				
			} else if(false) {
				
//            # Leave line breaks in.
//            $output .= $text;
				
			} else {
				
				// Format non-code text.

				// Convert linked images.
				
//            	if ($text =~ /<img mode=\"link\"/)
				
				if(false) {
				
//                if ($style == NDMARKUPTOHTML_GENERAL)
//                    {
//                    # Split by tags we would want to see the linked images appear after.  For example, an image link appearing in
//                    # the middle of a paragraph would appear after the end of that paragraph.
//                    my @imageBlocks = split(/(<p>.*?<\/p>|<dl>.*?<\/dl>|<ul>.*?<\/ul>)/, $text);
//                    $text = undef;
//
//                    foreach my $imageBlock (@imageBlocks)
//                        {
//                        $imageBlock =~ s{<img mode=\"link\" target=\"([^\"]*)\" original=\"([^\"]*)\">}
//                                                {$self->BuildImage($sourceFile, 'link', $1, $2)}ge;
//
//                        $text .= $imageBlock . $imageContent;
//                        $imageContent = undef;
//                        };
//                    }
//
//                # Use only the text for tooltips and summaries.
//                else
//                    {
//                    $text =~ s{<img mode=\"link\" target=\"[^\"]*\" original=\"([^\"]*)\">}{$1}g;
//                    };
					
				}
				
//            # Convert quotes to fancy quotes.  This has to be done before links because some of them may have JavaScript
//            # attributes that use the apostrophe character.
//            $text =~ s/^\'/&lsquo;/gm;
//            $text =~ s/([\ \(\[\{])\'/$1&lsquo;/g;
//            $text =~ s/\'/&rsquo;/g;
//
//            $text =~ s/^&quot;/&ldquo;/gm;
//            $text =~ s/([\ \(\[\{])&quot;/$1&ldquo;/g;
//            $text =~ s/&quot;/&rdquo;/g;
//
//            # Resolve and convert links, except for tooltips.
//            if ($style != NDMARKUPTOHTML_TOOLTIP)
				if(true) {
					
					while(true) {
						Matcher matcher = patternLink.matcher(text) ;
						if(matcher.find()) {
							String newText = "" ;
							if(matcher.start() != 0) {
								newText += text.substring(0, matcher.start()) ;
							}
							newText += buildTextLink(docFile, docTopic, matcher.group(1), matcher.group(2), matcher.group(3)) ;
							if(!matcher.hitEnd()) {
								newText += text.substring(matcher.end()) ;
							}
							text = newText ;
						} else {
							break ;
						}
					}

//                $text =~ s{<link target=\"([^\"]*)\" name=\"([^\"]*)\" original=\"([^\"]*)\">}
//                               {$self->BuildTextLink($1, $2, $3, $package, $using, $sourceFile)}ge;
//					text.replaceAll("\\<link target=\"([^\"]*)\" name=\"([^\"]*)\" original=\"([^\"]*)\"\\>,"") ;
					
//                $text =~ s/<url target=\"([^\"]*)\" name=\"([^\"]*)\">/$self->BuildURLLink($1, $2)/ge;

				} else {

//                $text =~ s{<link target=\"[^\"]*\" name=\"([^\"]*)\" original=\"[^\"]*\">}{$1}g;
//                $text =~ s{<url target=\"[^\"]*\" name=\"([^\"]*)\">}{$1}g;

				}
//
//            # We do full e-mail links anyway just so the obfuscation remains.
//            $text =~ s/<email target=\"([^\"]*)\" name=\"([^\"]*)\">/$self->BuildEMailLink($1, $2)/ge;
//
//
//            # Convert inline images, but only for the general style.
//            if ($style == NDMARKUPTOHTML_GENERAL)
//                {
//                $text =~ s{<img mode=\"inline\" target=\"([^\"]*)\" original=\"([^\"]*)\">}
//                               {$self->BuildImage($sourceFile, 'inline', $1, $2)}ge;
//                }
//            else
//                {
//                $text =~ s{<img mode=\"inline\" target=\"[^\"]*\" original=\"([^\"]*)\">}{$1}g;
//                };
//
//            # Copyright symbols.  Prevent conversion when part of (a), (b), (c) lists.
//            if ($text !~ /\(a\)/i)
//                {  $text =~ s/\(c\)/&copy;/gi;  };
//
//            # Trademark symbols.
//            $text =~ s/\(tm\)/&trade;/gi;
//            $text =~ s/\(r\)/&reg;/gi;
//
//            # Add double spaces too.
//            $text = $self->AddDoubleSpaces($text);
//
				// Headings
				text = text.replaceAll("\\<h\\>","<h4 class=CHeading>") ;
				text = text.replaceAll("\\</h\\>","</h4>") ;
//
//            # Description Lists
//            $text =~ s/<dl>/<table border=0 cellspacing=0 cellpadding=0 class=CDescriptionList>/g;
//            $text =~ s/<\/dl>/<\/table>/g;
//
//            $text =~ s/<de>/<tr><td class=CDLEntry>/g;
//            $text =~ s/<\/de>/<\/td>/g;
//
//            if ($dlSymbolBehavior == ::ENUM_GLOBAL())
//                {  $text =~ s/<ds>([^<]+)<\/ds>/$self->MakeDescriptionListSymbol(undef, $1)/ge;  }
//            elsif ($dlSymbolBehavior == ::ENUM_UNDER_PARENT())
//                {  $text =~ s/<ds>([^<]+)<\/ds>/$self->MakeDescriptionListSymbol($package, $1)/ge;  }
//            else # ($dlSymbolBehavior == ::ENUM_UNDER_TYPE())
//                {  $text =~ s/<ds>([^<]+)<\/ds>/$self->MakeDescriptionListSymbol($symbol, $1)/ge;  }
//
//            sub MakeDescriptionListSymbol #(package, text)
//                {
//                my ($self, $package, $text) = @_;
//
//                $text = NaturalDocs::NDMarkup->RestoreAmpChars($text);
//                my $symbol = NaturalDocs::SymbolString->FromText($text);
//
//                if (defined $package)
//                    {  $symbol = NaturalDocs::SymbolString->Join($package, $symbol);  };
//
//                return
//                '<tr>'
//                    . '<td class=CDLEntry>'
//                        # The anchors are closed, but not around the text, to prevent the :hover CSS style from kicking in.
//                        . '<a name="' . $self->SymbolToHTMLSymbol($symbol) . '"></a>'
//                        . $text
//                    . '</td>';
//                };
//
//            $text =~ s/<dd>/<td class=CDLDescription>/g;
//            $text =~ s/<\/dd>/<\/td><\/tr>/g;
				
				output += text ;
				
            }
			
			index++ ;
				
        }
		
		return output ;
	}

	private String buildTextLink(DocFile docFile, DocTopic docTopic, String target, String name, String original) {
		String plainTarget = HTMLUtils.restoreAmpChars(target) ;
		String symbol = SymbolTableEntry.cleanSymbol(plainTarget) ; // TODO: ND does some parsing on this
		SymbolTableEntry symbolTableEntry = model.getSymbolTable().resolveSymbol(docTopic,symbol) ;
		if(symbolTableEntry == null) {
			fLog.error(
					String.format("Failed to find symbol for link(%s) in docFile(%s)",
							symbol,
							docFile.getTitle())) ;
			return original ;
		} else	if(symbolTableEntry.getDocFile() == null) {
			fLog.error(
					String.format("Symbol(%s) appears in docFile(%s) appears to have no docFile",
							symbol,
							docFile.getTitle())) ;
			return original ;
		} else {
			String link ;
			String targetFile = null ;
			if(symbolTableEntry.getDocFile() != docFile) {
				targetFile = HTMLUtils.makeRelativeURL(
						docFile.getOutPath(), 
						symbolTableEntry.getDocFile().getOutPath(), 
						true) ;
			}
			link = "<a href=\"" ;
			if(targetFile != null) {
				link += targetFile ;
			}
			link 	+= "#" + symbolTableEntry.getSymbol() + "\"";
			link 	+= "class=L" + HTMLUtils.capitalize(symbolTableEntry.getTopicType()) ;
			link 	+= "> " + name ;
			link += "</a>" ;
			return link ;
		}
	}
	
}



