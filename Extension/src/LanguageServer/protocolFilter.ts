/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All Rights Reserved.
 * See 'LICENSE' in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';

import * as path from 'path';
import { Middleware } from 'vscode-languageclient';
import { ClientCollection } from './clientCollection';
import { Client } from './client';
import * as vscode from 'vscode';
import { CppSettings } from './settings';
import { onDidChangeActiveTextEditor, processDelayedDidOpen } from './extension';

export function createProtocolFilter(clients: ClientCollection): Middleware {
    // Disabling lint for invoke handlers
    let defaultHandler: (data: any, callback: (data: any) => void) => void = (data, callback: (data) => void) => { clients.ActiveClient.notifyWhenReady(() => callback(data)); };
    /* tslint:disable */
    // let invoke1 = (a, callback: (a) => any) => { if (clients.ActiveClient === me) { return me.requestWhenReady(() => callback(a)); } return null; };
    let invoke2 = (a, b, callback: (a, b) => any) => clients.ActiveClient.requestWhenReady(() => callback(a, b));
    let invoke3 = (a, b, c, callback: (a, b, c) => any) => clients.ActiveClient.requestWhenReady(() => callback(a, b, c));
    let invoke4 = (a, b, c, d, callback: (a, b, c, d) => any) => clients.ActiveClient.requestWhenReady(() => callback(a, b, c, d));
    let invoke5 = (a, b, c, d, e, callback: (a, b, c, d, e) => any) => clients.ActiveClient.requestWhenReady(() => callback(a, b, c, d, e));
    /* tslint:enable */

    return {
        didOpen: (document, sendMessage) => {
            let editor: vscode.TextEditor | undefined = vscode.window.visibleTextEditors.find(e => e.document === document);
            if (editor) {
                // If the file was visible editor when we were activated, we will not get a call to
                // onDidChangeVisibleTextEditors, so immediately open any file that is visible when we receive didOpen.
                // Otherwise, we defer opening the file until it's actually visible.
                let me: Client = clients.getClientFor(document.uri);
                if (clients.checkOwnership(me, document)) {
                    me.TrackedDocuments.add(document);
                    if ((document.uri.path.endsWith(".C") || document.uri.path.endsWith(".H")) && document.languageId === "c") {
                        let cppSettings: CppSettings = new CppSettings();
                        if (cppSettings.autoAddFileAssociations) {
                            const fileName: string = path.basename(document.uri.fsPath);
                            const mappingString: string = fileName + "@" + document.uri.fsPath;
                            me.addFileAssociations(mappingString, false);
                        }
                    }
                    me.provideCustomConfiguration(document.uri, undefined);
                    me.notifyWhenReady(() => {
                        sendMessage(document);
                        me.onDidOpenTextDocument(document);
                        if (editor && editor === vscode.window.activeTextEditor) {
                            onDidChangeActiveTextEditor(editor);
                        }
                    });
                }
            } else {
                // NO-OP
                // If the file is not opened into an editor (such as in response for a control-hover),
                // we do not actually load a translation unit for it.  When we receive a didOpen, the file
                // may not yet be visible.  So, we defer creation of the  translation until we receive a
                // call to onDidChangeVisibleTextEditors(), in extension.ts.  A file is only loaded when
                // it is actually opened in the editor (not in response to control-hover, which sends a
                // didOpen), and first becomes visible.
            }
        },
        didChange: (textDocumentChangeEvent, sendMessage) => {
            let me: Client = clients.getClientFor(textDocumentChangeEvent.document.uri);
            if (!me.TrackedDocuments.has(textDocumentChangeEvent.document)) {
                processDelayedDidOpen(textDocumentChangeEvent.document);
            }
            me.onDidChangeTextDocument(textDocumentChangeEvent);
            me.notifyWhenReady(() => sendMessage(textDocumentChangeEvent));
        },
        willSave: defaultHandler,
        willSaveWaitUntil: (event, sendMessage) => {
            let me: Client = clients.getClientFor(event.document.uri);
            if (me.TrackedDocuments.has(event.document)) {
                return me.requestWhenReady(() => sendMessage(event));
            }
            return Promise.resolve([]);
        },
        didSave: defaultHandler,
        didClose: (document, sendMessage) => {
            let me: Client = clients.getClientFor(document.uri);
            if (me.TrackedDocuments.has(document)) {
                me.onDidCloseTextDocument(document);
                me.TrackedDocuments.delete(document);
                me.notifyWhenReady(() => sendMessage(document));
            }
        },

        provideCompletionItem: invoke4,
        resolveCompletionItem: invoke2,
        provideHover: (document, position, token, next: (document, position, token) => any) => {
            let me: Client = clients.getClientFor(document.uri);
            if (clients.checkOwnership(me, document)) {
                return clients.ActiveClient.requestWhenReady(() => next(document, position, token));
            }
            return null;
        },
        provideSignatureHelp: invoke3,
        provideDefinition: invoke3,
        provideReferences: invoke4,
        provideDocumentHighlights: invoke3,
        provideDocumentSymbols: invoke2,
        provideWorkspaceSymbols: invoke2,
        provideCodeActions: invoke4,
        provideCodeLenses: invoke2,
        resolveCodeLens: invoke2,
        provideDocumentFormattingEdits: invoke3,
        provideDocumentRangeFormattingEdits: invoke4,
        provideOnTypeFormattingEdits: invoke5,
        provideRenameEdits: invoke4,
        provideDocumentLinks: invoke2,
        resolveDocumentLink: invoke2,
        provideDeclaration: invoke3

        // I believe the default handler will do the same thing.
        // workspace: {
        //     didChangeConfiguration: (sections, sendMessage) => sendMessage(sections)
        // }
    };
}
