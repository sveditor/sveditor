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

package net.sf.sveditor.core.docs.html ;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sf.sveditor.core.docs.model.DocFile;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.docs.model.SymbolTableEntry;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;



public class HTMLFromNDMarkup {
	
	private final static Pattern patternLink = 
			Pattern.compile("\\<link target=\"([^\"]*)\" name=\"([^\"]*)\" original=\"([^\"]*)\"\\>") ;
	
	public enum NDMarkupToHTMLStyle { Tooltip, General } ;
	
	private DocModel fModel ;
	private LogHandle fLog ;
	
	public HTMLFromNDMarkup() { 
		this(null) ;
	}
	
	public HTMLFromNDMarkup(DocModel model) {
		fModel = model ;
		fLog = LogFactory.getLogHandle("HTMLFromNDMarkup") ;
	}
	
	@SuppressWarnings("unused")
	public String convertNDMarkupToHTML(
			DocFile docFile, 
			DocTopic docTopic, 
			String markup, 
			NDMarkupToHTMLStyle style) {
		
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
				if(style != NDMarkupToHTMLStyle.Tooltip) {
					
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
					
//                $text =~ s/<url target=\"([^\"]*)\" name=\"([^\"]*)\">/$self->BuildURLLink($1, $2)/ge;

				} else {
					
					Matcher matcher = patternLink.matcher(text) ;
					
					text = matcher.replaceAll("$1") ;

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
		String symbol = SymbolTableEntry.cleanSymbol(plainTarget) ; 
		if(fModel == null) {
			fLog.error(String.format("buildTextLink needs a model")) ;
			return "" ;
		}
		SymbolTableEntry symbolTableEntry = fModel.getSymbolTable().resolveSymbol(docTopic,symbol) ;
		if(symbolTableEntry == null) {
//			fLog.error(
//					String.format("Failed to find symbol for link(%s) in docFile(%s)",
//							symbol,
//							docFile.getTitle())) ;
			fLog.debug(ILogLevel.LEVEL_MIN,
					String.format("Failed to find symbol for link(%s) in docFile(%s)",
							symbol,
							docFile.getTitle())) ;
			return original ;
		} else	if(symbolTableEntry.getDocFile() == null) {
//			fLog.error(
//					String.format("Symbol(%s) in docFile(%s) appears to have no docFile",
//							symbol,
//							docFile.getTitle())) ;
			fLog.debug(ILogLevel.LEVEL_MIN,
					String.format("Symbol(%s) in docFile(%s) appears to have no docFile",
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