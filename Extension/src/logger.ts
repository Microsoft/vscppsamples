/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All Rights Reserved.
 * See 'LICENSE' in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';

import * as vscode from 'vscode';
import * as os from 'os';
import { CppSettings } from './LanguageServer/settings';

// This is used for testing purposes
let Subscriber: (message: string) => void;
export function subscribeToAllLoggers(subscriber: (message: string) => void): void {
    Subscriber = subscriber;
}

export class Logger {
    private writer: (message: string) => void;

    constructor(writer: (message: string) => void) {
        this.writer = writer;
    }

    public append(message: string): void {
        this.writer(message);
        if (Subscriber) {
            Subscriber(message);
        }
    }

    public appendLine(message: string): void {
        this.writer(message + os.EOL);
        if (Subscriber) {
            Subscriber(message + os.EOL);
        }
    }

    // We should not await on this function.
    public showInformationMessage(message: string, items?: string[]): Thenable<string | undefined> {
        this.appendLine(message);

        if (!items) {
            return vscode.window.showInformationMessage(message);
        }
        return vscode.window.showInformationMessage(message, ...items);
    }

    // We should not await on this function.
    public showWarningMessage(message: string, items?: string[]): Thenable<string | undefined> {
        this.appendLine(message);

        if (!items) {
            return vscode.window.showWarningMessage(message);
        }
        return vscode.window.showWarningMessage(message, ...items);
    }

    // We should not await on this function.
    public showErrorMessage(message: string, items?: string[]): Thenable<string | undefined> {
        this.appendLine(message);

        if (!items) {
            return vscode.window.showErrorMessage(message);
        }
        return vscode.window.showErrorMessage(message, ...items);
    }
}

let outputChannel: vscode.OutputChannel | undefined;

export function getOutputChannel(): vscode.OutputChannel {
    if (!outputChannel) {
        outputChannel = vscode.window.createOutputChannel("C/C++");
        const settings: CppSettings = new CppSettings();
        const loggingLevel: string | undefined = settings.loggingLevel;
        if (!!loggingLevel && loggingLevel !== "None" && loggingLevel !== "Error") {
            outputChannel.appendLine(`loggingLevel: ${loggingLevel}`);
        }
    }
    return outputChannel;
}

export function showOutputChannel(): void {
    getOutputChannel().show();
}

let outputChannelLogger: Logger | undefined;

export function getOutputChannelLogger(): Logger {
    if (!outputChannelLogger) {
        outputChannelLogger = new Logger(message => getOutputChannel().append(message));
    }
    return outputChannelLogger;
}
