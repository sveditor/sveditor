#!/bin/env python3

license = """
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#  http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
"""

full_license_java = """
/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
"""

replace_license_java = """
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
"""

import os

def process_dir(d):
    for l in os.listdir(d):
        if l.endswith(".java"):
            has_license = False
            has_old_license = False
            content = ""
            with open(os.path.join(d, l), "r") as fp:
                # Look for an 'All rights reserved' or 'This program and the'
                #
                # - 'All rights reserved' means we have the old copyright
                # in the first few lines of the file
                content = ""
                for i in range(32):
                    line = fp.readline()
                    
                    if line == "":
                        break
                
                    if line.find("All rights reserved") != -1:
                        has_old_license = True
                        break
                    if line.find("This program and the") != -1:
                        has_license = True
                        break
                    content += line

                if has_old_license:
                    # File has the old license. Save the content,
                    # while skipping the old header.
                    
                    # Read until we find 'epl-v10'
                    for i in range(4):
                        line = fp.readline()

                        print("SKIP: " + line[:-1])
                        if line.find('epl-v10') != -1:
                            break

                    content += replace_license_java[1:]

                    # Now, read the rest of the file
                    while True:
                        line = fp.readline()
                        
                        if line == "":
                            break
                        else:
                            content += line
                elif not has_license:
                    # No license whatsoever. Need to insert
                    fp.seek(0)
                    content = full_license_java[1:]
                    content += fp.read()
                    
                        
            if has_old_license or not has_license:
                if has_old_license:
                    print("TODO: Need to replace license")
                else:
                    print("TODO: Need to add license")
                print("Content:\n" + content)
                
#                with open(os.path.join(d, l), "w") as fp:
#                    fp.write(content)
                    
        elif os.path.isdir(os.path.join(d, l)):
            process_dir(os.path.join(d, l))
    
def main():
    root_dir = os.path.dirname(os.path.abspath(os.path.dirname(__file__)))
    sveditor_dir = os.path.join(root_dir, "sveditor")
  
    process_dir(sveditor_dir)
  
if __name__ == "__main__":
  main()


