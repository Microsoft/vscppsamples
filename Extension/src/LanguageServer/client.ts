/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All Rights Reserved.
 * See 'LICENSE' in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';

import * as path from 'path';
import * as vscode from 'vscode';

// Importing providers here
import { OnTypeFormattingEditProvider } from './Providers/onTypeFormattingEditProvider';
import { FoldingRangeProvider } from './Providers/foldingRangeProvider';
import { SemanticTokensProvider } from './Providers/semanticTokensProvider';
import { DocumentFormattingEditProvider } from './Providers/documentFormattingEditProvider';
import { DocumentRangeFormattingEditProvider } from './Providers/documentRangeFormattingEditProvider';
import { DocumentSymbolProvider } from './Providers/documentSymbolProvider';
import { WorkspaceSymbolProvider } from './Providers/workspaceSymbolProvider';
import { RenameProvider } from './Providers/renameProvider';
import { FindAllReferencesProvider } from './Providers/findAllReferencesProvider';
// End provider imports

import { LanguageClient, LanguageClientOptions, ServerOptions, NotificationType, TextDocumentIdentifier, RequestType, ErrorAction, CloseAction, DidOpenTextDocumentParams, Range, Position, DocumentFilter } from 'vscode-languageclient';
import { SourceFileConfigurationItem, WorkspaceBrowseConfiguration, SourceFileConfiguration, Version } from 'vscode-cpptools';
import { Status, IntelliSenseStatus } from 'vscode-cpptools/out/testApi';
import * as util from '../common';
import * as configs from './configurations';
import { CppSettings, OtherSettings } from './settings';
import * as telemetry from '../telemetry';
import { PersistentState, PersistentFolderState } from './persistentState';
import { UI, getUI } from './ui';
import { ClientCollection } from './clientCollection';
import { createProtocolFilter } from './protocolFilter';
import { DataBinding } from './dataBinding';
import minimatch = require("minimatch");
import * as logger from '../logger';
import { updateLanguageConfigurations, registerCommands } from './extension';
import { SettingsTracker, getTracker } from './settingsTracker';
import { getTestHook, TestHook } from '../testHook';
import { getCustomConfigProviders, CustomConfigurationProvider1, isSameProviderExtensionId } from '../LanguageServer/customProviders';
import * as fs from 'fs';
import * as os from 'os';
import * as refs from './references';
import * as nls from 'vscode-nls';
import { lookupString, localizedStringCount } from '../nativeStrings';

nls.config({ messageFormat: nls.MessageFormat.bundle, bundleFormat: nls.BundleFormat.standalone })();
const localize: nls.LocalizeFunc = nls.loadMessageBundle();
type LocalizeStringParams = util.LocalizeStringParams;

let ui: UI;
let timeStamp: number = 0;
const configProviderTimeout: number = 2000;

// Data shared by all clients.
let languageClient: LanguageClient;
let languageClientCrashedNeedsRestart: boolean = false;
const languageClientCrashTimes: number[] = [];
let clientCollection: ClientCollection;
let pendingTask: util.BlockingTask<any> | undefined;
let compilerDefaults: configs.CompilerDefaults;
let diagnosticsChannel: vscode.OutputChannel;
let outputChannel: vscode.OutputChannel;
let debugChannel: vscode.OutputChannel;
let warningChannel: vscode.OutputChannel;
let diagnosticsCollection: vscode.DiagnosticCollection;
let workspaceDisposables: vscode.Disposable[] = [];
export let workspaceReferences: refs.ReferencesManager;
export const openFileVersions: Map<string, number> = new Map<string, number>();
export const cachedEditorConfigSettings: Map<string, any> = new Map<string, any>();

export function disposeWorkspaceData(): void {
    workspaceDisposables.forEach((d) => d.dispose());
    workspaceDisposables = [];
}

function logTelemetry(notificationBody: TelemetryPayload): void {
    telemetry.logLanguageServerEvent(notificationBody.event, notificationBody.properties, notificationBody.metrics);
}

/**
 * listen for logging messages from the language server and print them to the Output window
 */
function setupOutputHandlers(): void {
    console.assert(languageClient !== undefined, "This method must not be called until this.languageClient is set in \"onReady\"");

    languageClient.onNotification(DebugProtocolNotification, (output) => {
        if (!debugChannel) {
            debugChannel = vscode.window.createOutputChannel(`${localize("c.cpp.debug.protocol", "C/C++ Debug Protocol")}`);
            workspaceDisposables.push(debugChannel);
        }
        debugChannel.appendLine("");
        debugChannel.appendLine("************************************************************************************************************************");
        debugChannel.append(`${output}`);
    });

    languageClient.onNotification(DebugLogNotification, logLocalized);
}

function log(output: string): void {
    if (!outputChannel) {
        outputChannel = logger.getOutputChannel();
        workspaceDisposables.push(outputChannel);
    }
    outputChannel.appendLine(`${output}`);
}

function logLocalized(params: LocalizeStringParams): void {
    const output: string = util.getLocalizedString(params);
    log(output);
}

/** Note: We should not await on the following functions,
 * or any funstion that returns a promise acquired from them,
 * vscode.window.showInformationMessage, vscode.window.showWarningMessage, vscode.window.showErrorMessage
*/
function showMessageWindow(params: ShowMessageWindowParams): void {
    const message: string = util.getLocalizedString(params.localizeStringParams);
    switch (params.type) {
        case 1: // Error
            vscode.window.showErrorMessage(message);
            break;
        case 2: // Warning
            vscode.window.showWarningMessage(message);
            break;
        case 3: // Info
            vscode.window.showInformationMessage(message);
            break;
        default:
            console.assert("Unrecognized type for showMessageWindow");
            break;
    }
}

function showWarning(params: ShowWarningParams): void {
    const message: string = util.getLocalizedString(params.localizeStringParams);
    let showChannel: boolean = false;
    if (!warningChannel) {
        warningChannel = vscode.window.createOutputChannel(`${localize("c.cpp.warnings", "C/C++ Configuration Warnings")}`);
        workspaceDisposables.push(warningChannel);
        showChannel = true;
    }
    // Append before showing the channel, to avoid a delay.
    warningChannel.appendLine(`[${new Date().toLocaleString()}] ${message}`);
    if (showChannel) {
        warningChannel.show(true);
    }
}

function publishDiagnostics(params: PublishDiagnosticsParams): void {
    if (!diagnosticsCollection) {
        diagnosticsCollection = vscode.languages.createDiagnosticCollection("C/C++");
    }

    // Convert from our Diagnostic objects to vscode Diagnostic objects
    const diagnostics: vscode.Diagnostic[] = [];
    params.diagnostics.forEach((d) => {
        const message: string = util.getLocalizedString(d.localizeStringParams);
        const r: vscode.Range = new vscode.Range(d.range.start.line, d.range.start.character, d.range.end.line, d.range.end.character);
        const diagnostic: vscode.Diagnostic = new vscode.Diagnostic(r, message, d.severity);
        diagnostic.code = d.code;
        diagnostic.source = d.source;
        diagnostics.push(diagnostic);
    });

    const realUri: vscode.Uri = vscode.Uri.parse(params.uri);
    diagnosticsCollection.set(realUri, diagnostics);

    clientCollection.timeTelemetryCollector.setUpdateRangeTime(realUri);
}

interface WorkspaceFolderParams {
    workspaceFolderUri?: string;
}

interface TelemetryPayload {
    event: string;
    properties?: { [key: string]: string };
    metrics?: { [key: string]: number };
}

interface DebugProtocolParams {
    jsonrpc: string;
    method: string;
    params?: any;
}

interface ReportStatusNotificationBody extends WorkspaceFolderParams {
    status: string;
}

interface QueryCompilerDefaultsParams {
}

interface CppPropertiesParams extends WorkspaceFolderParams {
    currentConfiguration: number;
    configurations: any[];
    isReady?: boolean;
}

interface FolderSelectedSettingParams extends WorkspaceFolderParams {
    currentConfiguration: number;
}

interface SwitchHeaderSourceParams extends WorkspaceFolderParams {
    switchHeaderSourceFileName: string;
}

interface FileChangedParams extends WorkspaceFolderParams {
    uri: string;
}

interface InputRegion {
    startLine: number;
    endLine: number;
}

interface DecorationRangesPair {
    decoration: vscode.TextEditorDecorationType;
    ranges: vscode.Range[];
}

interface InactiveRegionParams {
    uri: string;
    fileVersion: number;
    regions: InputRegion[];
}

// Need to convert vscode.Uri to a string before sending it to the language server.
interface SourceFileConfigurationItemAdapter {
    uri: string;
    configuration: SourceFileConfiguration;
}

interface CustomConfigurationParams extends WorkspaceFolderParams {
    configurationItems: SourceFileConfigurationItemAdapter[];
}

interface CustomBrowseConfigurationParams extends WorkspaceFolderParams {
    browseConfiguration: WorkspaceBrowseConfiguration;
}

interface CompileCommandsPaths extends WorkspaceFolderParams {
    paths: string[];
}

interface QueryTranslationUnitSourceParams extends WorkspaceFolderParams {
    uri: string;
}

interface QueryTranslationUnitSourceResult {
    candidates: string[];
}

interface GetDiagnosticsResult {
    diagnostics: string;
}

interface Diagnostic {
    range: Range;
    code?: number | string;
    source?: string;
    severity: vscode.DiagnosticSeverity;
    localizeStringParams: LocalizeStringParams;
}

interface PublishDiagnosticsParams {
    uri: string;
    diagnostics: Diagnostic[];
}

interface GetCodeActionsRequestParams {
    uri: string;
    range: Range;
}

interface CodeActionCommand {
    localizeStringParams: LocalizeStringParams;
    command: string;
    arguments?: any[];
    edit?: TextEdit;
}

interface ShowMessageWindowParams {
    type: number;
    localizeStringParams: LocalizeStringParams;
}

interface ShowWarningParams {
    localizeStringParams: LocalizeStringParams;
}

export interface GetDocumentSymbolRequestParams {
    uri: string;
}

export interface WorkspaceSymbolParams extends WorkspaceFolderParams {
    query: string;
}

export enum SymbolScope {
    Public = 0,
    Protected = 1,
    Private = 2
}

export interface LocalizeDocumentSymbol {
    name: string;
    detail: LocalizeStringParams;
    kind: vscode.SymbolKind;
    scope: SymbolScope;
    range: Range;
    selectionRange: Range;
    children: LocalizeDocumentSymbol[];
}

/** Differs from vscode.Location, which has a uri of type vscode.Uri. */
interface Location {
    uri: string;
    range: Range;
}

export interface LocalizeSymbolInformation {
    name: string;
    kind: vscode.SymbolKind;
    scope: SymbolScope;
    location: Location;
    containerName: string;
    suffix: LocalizeStringParams;
}

export interface RenameParams {
    newName: string;
    position: Position;
    textDocument: TextDocumentIdentifier;
}

export interface FindAllReferencesParams {
    position: Position;
    textDocument: TextDocumentIdentifier;
}

interface DidChangeConfigurationParams extends WorkspaceFolderParams {
    settings: any;
}

export interface FormatParams {
    uri: string;
    range: Range;
    character: string;
    insertSpaces: boolean;
    tabSize: number;
    settings: any;
}

interface TextEdit {
    range: Range;
    newText: string;
}

export interface GetFoldingRangesParams {
    uri: string;
    id: number;
}

export enum FoldingRangeKind {
    None = 0,
    Comment = 1,
    Imports = 2,
    Region = 3
}

export interface CppFoldingRange {
    kind: FoldingRangeKind;
    range: Range;
}

export interface GetFoldingRangesResult {
    canceled: boolean;
    ranges: CppFoldingRange[];
}

interface AbortRequestParams {
    id: number;
}

export interface GetSemanticTokensParams {
    uri: string;
    id: number;
}

interface SemanticToken {
    line: number;
    character: number;
    length: number;
    type: number;
    modifiers?: number;
}

export interface GetSemanticTokensResult {
    fileVersion: number;
    canceled: boolean;
    tokens: SemanticToken[];
}

enum SemanticTokenTypes {
    // These are camelCase as the enum names are used directly as strings in our legend.
    macro = 0,
    enumMember = 1,
    variable = 2,
    parameter = 3,
    type = 4,
    referenceType = 5,
    valueType = 6,
    function = 7,
    method = 8,
    property = 9,
    cliProperty = 10,
    event = 11,
    genericType = 12,
    templateFunction = 13,
    templateType = 14,
    namespace = 15,
    label = 16,
    customLiteral = 17,
    numberLiteral = 18,
    stringLiteral = 19,
    operatorOverload = 20,
    memberOperatorOverload = 21,
    newOperator = 22
}

enum SemanticTokenModifiers {
    // These are camelCase as the enum names are used directly as strings in our legend.
    // eslint-disable-next-line no-bitwise
    static = (1 << 0),
    // eslint-disable-next-line no-bitwise
    global = (1 << 1),
    // eslint-disable-next-line no-bitwise
    local = (1 << 2)
}

interface IntelliSenseSetup {
    uri: string;
}

interface GoToDirectiveInGroupParams {
    uri: string;
    position: Position;
    next: boolean;
};

interface SetTemporaryTextDocumentLanguageParams {
    path: string;
    isC: boolean;
    isCuda: boolean;
}

// Requests
const QueryCompilerDefaultsRequest: RequestType<QueryCompilerDefaultsParams, configs.CompilerDefaults, void, void> = new RequestType<QueryCompilerDefaultsParams, configs.CompilerDefaults, void, void>('cpptools/queryCompilerDefaults');
const QueryTranslationUnitSourceRequest: RequestType<QueryTranslationUnitSourceParams, QueryTranslationUnitSourceResult, void, void> = new RequestType<QueryTranslationUnitSourceParams, QueryTranslationUnitSourceResult, void, void>('cpptools/queryTranslationUnitSource');
const SwitchHeaderSourceRequest: RequestType<SwitchHeaderSourceParams, string, void, void> = new RequestType<SwitchHeaderSourceParams, string, void, void>('cpptools/didSwitchHeaderSource');
const GetDiagnosticsRequest: RequestType<void, GetDiagnosticsResult, void, void> = new RequestType<void, GetDiagnosticsResult, void, void>('cpptools/getDiagnostics');
const GetCodeActionsRequest: RequestType<GetCodeActionsRequestParams, CodeActionCommand[], void, void> = new RequestType<GetCodeActionsRequestParams, CodeActionCommand[], void, void>('cpptools/getCodeActions');
export const GetDocumentSymbolRequest: RequestType<GetDocumentSymbolRequestParams, LocalizeDocumentSymbol[], void, void> = new RequestType<GetDocumentSymbolRequestParams, LocalizeDocumentSymbol[], void, void>('cpptools/getDocumentSymbols');
export const GetSymbolInfoRequest: RequestType<WorkspaceSymbolParams, LocalizeSymbolInformation[], void, void> = new RequestType<WorkspaceSymbolParams, LocalizeSymbolInformation[], void, void>('cpptools/getWorkspaceSymbols');
export const GetFoldingRangesRequest: RequestType<GetFoldingRangesParams, GetFoldingRangesResult, void, void> = new RequestType<GetFoldingRangesParams, GetFoldingRangesResult, void, void>('cpptools/getFoldingRanges');
export const GetSemanticTokensRequest: RequestType<GetSemanticTokensParams, GetSemanticTokensResult, void, void> = new RequestType<GetSemanticTokensParams, GetSemanticTokensResult, void, void>('cpptools/getSemanticTokens');
export const FormatDocumentRequest: RequestType<FormatParams, TextEdit[], void, void> = new RequestType<FormatParams, TextEdit[], void, void>('cpptools/formatDocument');
export const FormatRangeRequest: RequestType<FormatParams, TextEdit[], void, void> = new RequestType<FormatParams, TextEdit[], void, void>('cpptools/formatRange');
export const FormatOnTypeRequest: RequestType<FormatParams, TextEdit[], void, void> = new RequestType<FormatParams, TextEdit[], void, void>('cpptools/formatOnType');
const GoToDirectiveInGroupRequest: RequestType<GoToDirectiveInGroupParams, Position | undefined, void, void> = new RequestType<GoToDirectiveInGroupParams, Position | undefined, void, void>('cpptools/goToDirectiveInGroup');

// Notifications to the server
const DidOpenNotification: NotificationType<DidOpenTextDocumentParams, void> = new NotificationType<DidOpenTextDocumentParams, void>('textDocument/didOpen');
const FileCreatedNotification: NotificationType<FileChangedParams, void> = new NotificationType<FileChangedParams, void>('cpptools/fileCreated');
const FileChangedNotification: NotificationType<FileChangedParams, void> = new NotificationType<FileChangedParams, void>('cpptools/fileChanged');
const FileDeletedNotification: NotificationType<FileChangedParams, void> = new NotificationType<FileChangedParams, void>('cpptools/fileDeleted');
const ResetDatabaseNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/resetDatabase');
const PauseParsingNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/pauseParsing');
const ResumeParsingNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/resumeParsing');
const ActiveDocumentChangeNotification: NotificationType<TextDocumentIdentifier, void> = new NotificationType<TextDocumentIdentifier, void>('cpptools/activeDocumentChange');
const TextEditorSelectionChangeNotification: NotificationType<Range, void> = new NotificationType<Range, void>('cpptools/textEditorSelectionChange');
const ChangeCppPropertiesNotification: NotificationType<CppPropertiesParams, void> = new NotificationType<CppPropertiesParams, void>('cpptools/didChangeCppProperties');
const ChangeCompileCommandsNotification: NotificationType<FileChangedParams, void> = new NotificationType<FileChangedParams, void>('cpptools/didChangeCompileCommands');
const ChangeSelectedSettingNotification: NotificationType<FolderSelectedSettingParams, void> = new NotificationType<FolderSelectedSettingParams, void>('cpptools/didChangeSelectedSetting');
const IntervalTimerNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/onIntervalTimer');
const CustomConfigurationNotification: NotificationType<CustomConfigurationParams, void> = new NotificationType<CustomConfigurationParams, void>('cpptools/didChangeCustomConfiguration');
const CustomBrowseConfigurationNotification: NotificationType<CustomBrowseConfigurationParams, void> = new NotificationType<CustomBrowseConfigurationParams, void>('cpptools/didChangeCustomBrowseConfiguration');
const ClearCustomConfigurationsNotification: NotificationType<WorkspaceFolderParams, void> = new NotificationType<WorkspaceFolderParams, void>('cpptools/clearCustomConfigurations');
const ClearCustomBrowseConfigurationNotification: NotificationType<WorkspaceFolderParams, void> = new NotificationType<WorkspaceFolderParams, void>('cpptools/clearCustomBrowseConfiguration');
const RescanFolderNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/rescanFolder');
export const RequestReferencesNotification: NotificationType<boolean, void> = new NotificationType<boolean, void>('cpptools/requestReferences');
export const CancelReferencesNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/cancelReferences');
const FinishedRequestCustomConfig: NotificationType<string, void> = new NotificationType<string, void>('cpptools/finishedRequestCustomConfig');
const FindAllReferencesNotification: NotificationType<FindAllReferencesParams, void> = new NotificationType<FindAllReferencesParams, void>('cpptools/findAllReferences');
const RenameNotification: NotificationType<RenameParams, void> = new NotificationType<RenameParams, void>('cpptools/rename');
const DidChangeSettingsNotification: NotificationType<DidChangeConfigurationParams, void> = new NotificationType<DidChangeConfigurationParams, void>('cpptools/didChangeSettings');
const AbortRequestNotification: NotificationType<AbortRequestParams, void> = new NotificationType<AbortRequestParams, void>('cpptools/abortRequest');

// Notifications from the server
const ReloadWindowNotification: NotificationType<void, void> = new NotificationType<void, void>('cpptools/reloadWindow');
const LogTelemetryNotification: NotificationType<TelemetryPayload, void> = new NotificationType<TelemetryPayload, void>('cpptools/logTelemetry');
const ReportTagParseStatusNotification: NotificationType<LocalizeStringParams, void> = new NotificationType<LocalizeStringParams, void>('cpptools/reportTagParseStatus');
const ReportStatusNotification: NotificationType<ReportStatusNotificationBody, void> = new NotificationType<ReportStatusNotificationBody, void>('cpptools/reportStatus');
const DebugProtocolNotification: NotificationType<DebugProtocolParams, void> = new NotificationType<DebugProtocolParams, void>('cpptools/debugProtocol');
const DebugLogNotification: NotificationType<LocalizeStringParams, void> = new NotificationType<LocalizeStringParams, void>('cpptools/debugLog');
const InactiveRegionNotification: NotificationType<InactiveRegionParams, void> = new NotificationType<InactiveRegionParams, void>('cpptools/inactiveRegions');
const CompileCommandsPathsNotification: NotificationType<CompileCommandsPaths, void> = new NotificationType<CompileCommandsPaths, void>('cpptools/compileCommandsPaths');
const ReferencesNotification: NotificationType<refs.ReferencesResultMessage, void> = new NotificationType<refs.ReferencesResultMessage, void>('cpptools/references');
const ReportReferencesProgressNotification: NotificationType<refs.ReportReferencesProgressNotification, void> = new NotificationType<refs.ReportReferencesProgressNotification, void>('cpptools/reportReferencesProgress');
const RequestCustomConfig: NotificationType<string, void> = new NotificationType<string, void>('cpptools/requestCustomConfig');
const PublishDiagnosticsNotification: NotificationType<PublishDiagnosticsParams, void> = new NotificationType<PublishDiagnosticsParams, void>('cpptools/publishDiagnostics');
const ShowMessageWindowNotification: NotificationType<ShowMessageWindowParams, void> = new NotificationType<ShowMessageWindowParams, void>('cpptools/showMessageWindow');
const ShowWarningNotification: NotificationType<ShowWarningParams, void> = new NotificationType<ShowWarningParams, void>('cpptools/showWarning');
const ReportTextDocumentLanguage: NotificationType<string, void> = new NotificationType<string, void>('cpptools/reportTextDocumentLanguage');
const SemanticTokensChanged: NotificationType<string, void> = new NotificationType<string, void>('cpptools/semanticTokensChanged');
const IntelliSenseSetupNotification: NotificationType<IntelliSenseSetup, void> = new NotificationType<IntelliSenseSetup, void>('cpptools/IntelliSenseSetup');
const SetTemporaryTextDocumentLanguageNotification: NotificationType<SetTemporaryTextDocumentLanguageParams, void> = new NotificationType<SetTemporaryTextDocumentLanguageParams, void>('cpptools/setTemporaryTextDocumentLanguage');

let failureMessageShown: boolean = false;

export interface ReferencesCancellationState {
    reject(): void;
    callback(): void;
}

class ClientModel {
    public isTagParsing: DataBinding<boolean>;
    public isUpdatingIntelliSense: DataBinding<boolean>;
    public referencesCommandMode: DataBinding<refs.ReferencesCommandMode>;
    public tagParserStatus: DataBinding<string>;
    public activeConfigName: DataBinding<string>;

    constructor() {
        this.isTagParsing = new DataBinding<boolean>(false);
        this.isUpdatingIntelliSense = new DataBinding<boolean>(false);
        this.referencesCommandMode = new DataBinding<refs.ReferencesCommandMode>(refs.ReferencesCommandMode.None);
        this.tagParserStatus = new DataBinding<string>("");
        this.activeConfigName = new DataBinding<string>("");
    }

    public activate(): void {
        this.isTagParsing.activate();
        this.isUpdatingIntelliSense.activate();
        this.referencesCommandMode.activate();
        this.tagParserStatus.activate();
        this.activeConfigName.activate();
    }

    public deactivate(): void {
        this.isTagParsing.deactivate();
        this.isUpdatingIntelliSense.deactivate();
        this.referencesCommandMode.deactivate();
        this.tagParserStatus.deactivate();
        this.activeConfigName.deactivate();
    }

    public dispose(): void {
        this.isTagParsing.dispose();
        this.isUpdatingIntelliSense.dispose();
        this.referencesCommandMode.dispose();
        this.tagParserStatus.dispose();
        this.activeConfigName.dispose();
    }
}

export interface Client {
    TagParsingChanged: vscode.Event<boolean>;
    IntelliSenseParsingChanged: vscode.Event<boolean>;
    ReferencesCommandModeChanged: vscode.Event<refs.ReferencesCommandMode>;
    TagParserStatusChanged: vscode.Event<string>;
    ActiveConfigChanged: vscode.Event<string>;
    RootPath: string;
    RootRealPath: string;
    RootUri?: vscode.Uri;
    Name: string;
    TrackedDocuments: Set<vscode.TextDocument>;
    onDidChangeSettings(event: vscode.ConfigurationChangeEvent, isFirstClient: boolean): { [key: string]: string };
    onDidOpenTextDocument(document: vscode.TextDocument): void;
    onDidCloseTextDocument(document: vscode.TextDocument): void;
    onDidChangeVisibleTextEditors(editors: vscode.TextEditor[]): void;
    onDidChangeTextDocument(textDocumentChangeEvent: vscode.TextDocumentChangeEvent): void;
    onRegisterCustomConfigurationProvider(provider: CustomConfigurationProvider1): Thenable<void>;
    updateCustomConfigurations(requestingProvider?: CustomConfigurationProvider1): Thenable<void>;
    updateCustomBrowseConfiguration(requestingProvider?: CustomConfigurationProvider1): Thenable<void>;
    provideCustomConfiguration(docUri: vscode.Uri, requestFile?: string): Promise<void>;
    logDiagnostics(): Promise<void>;
    rescanFolder(): Promise<void>;
    toggleReferenceResultsView(): void;
    setCurrentConfigName(configurationName: string): Thenable<void>;
    getCurrentConfigName(): Thenable<string | undefined>;
    getCurrentConfigCustomVariable(variableName: string): Thenable<string>;
    getVcpkgInstalled(): Thenable<boolean>;
    getVcpkgEnabled(): Thenable<boolean>;
    getCurrentCompilerPathAndArgs(): Thenable<util.CompilerPathAndArgs | undefined>;
    getKnownCompilers(): Thenable<configs.KnownCompiler[] | undefined>;
    takeOwnership(document: vscode.TextDocument): void;
    queueTask<T>(task: () => Thenable<T>): Promise<T>;
    requestWhenReady<T>(request: () => Thenable<T>): Thenable<T>;
    notifyWhenLanguageClientReady(notify: () => void): void;
    awaitUntilLanguageClientReady(): void;
    requestSwitchHeaderSource(rootPath: string, fileName: string): Thenable<string>;
    activeDocumentChanged(document: vscode.TextDocument): void;
    activate(): void;
    selectionChanged(selection: Range): void;
    resetDatabase(): void;
    deactivate(): void;
    pauseParsing(): void;
    resumeParsing(): void;
    handleConfigurationSelectCommand(): Promise<void>;
    handleConfigurationProviderSelectCommand(): Promise<void>;
    handleShowParsingCommands(): Promise<void>;
    handleReferencesIcon(): void;
    handleConfigurationEditCommand(viewColumn?: vscode.ViewColumn): void;
    handleConfigurationEditJSONCommand(viewColumn?: vscode.ViewColumn): void;
    handleConfigurationEditUICommand(viewColumn?: vscode.ViewColumn): void;
    handleAddToIncludePathCommand(path: string): void;
    handleGoToDirectiveInGroup(next: boolean): Promise<void>;
    handleCheckForCompiler(): Promise<void>;
    onInterval(): void;
    dispose(): void;
    addFileAssociations(fileAssociations: string, languageId: string): void;
    sendDidChangeSettings(settings: any): void;
}

export function createClient(allClients: ClientCollection, workspaceFolder?: vscode.WorkspaceFolder): Client {
    return new DefaultClient(allClients, workspaceFolder);
}

export function createNullClient(): Client {
    return new NullClient();
}

export class DefaultClient implements Client {
    private innerLanguageClient?: LanguageClient; // The "client" that launches and communicates with our language "server" process.
    private disposables: vscode.Disposable[] = [];
    private documentFormattingProviderDisposable: vscode.Disposable | undefined;
    private formattingRangeProviderDisposable: vscode.Disposable | undefined;
    private onTypeFormattingProviderDisposable: vscode.Disposable | undefined;
    private codeFoldingProvider: FoldingRangeProvider | undefined;
    private codeFoldingProviderDisposable: vscode.Disposable | undefined;
    private semanticTokensProvider: SemanticTokensProvider | undefined;
    private semanticTokensProviderDisposable: vscode.Disposable | undefined;
    private innerConfiguration?: configs.CppProperties;
    private rootPathFileWatcher?: vscode.FileSystemWatcher;
    private rootFolder?: vscode.WorkspaceFolder;
    private rootRealPath: string;
    private storagePath: string;
    private trackedDocuments = new Set<vscode.TextDocument>();
    private isSupported: boolean = true;
    private inactiveRegionsDecorations = new Map<string, DecorationRangesPair>();
    private settingsTracker: SettingsTracker;
    private loggingLevel: string | undefined;
    private configurationProvider?: string;
    private documentSelector: DocumentFilter[] = [
        { scheme: 'file', language: 'c' },
        { scheme: 'file', language: 'cpp' },
        { scheme: 'file', language: 'cuda-cpp' }
    ];
    public semanticTokensLegend: vscode.SemanticTokensLegend | undefined;

    public static abortRequestId: number = 0;

    public static referencesParams: RenameParams | FindAllReferencesParams | undefined;
    public static referencesRequestPending: boolean = false;
    public static referencesPendingCancellations: ReferencesCancellationState[] = [];

    public static renameRequestsPending: number = 0;
    public static renamePending: boolean = false;

    // The "model" that is displayed via the UI (status bar).
    private model: ClientModel = new ClientModel();

    public get TagParsingChanged(): vscode.Event<boolean> { return this.model.isTagParsing.ValueChanged; }
    public get IntelliSenseParsingChanged(): vscode.Event<boolean> { return this.model.isUpdatingIntelliSense.ValueChanged; }
    public get ReferencesCommandModeChanged(): vscode.Event<refs.ReferencesCommandMode> { return this.model.referencesCommandMode.ValueChanged; }
    public get TagParserStatusChanged(): vscode.Event<string> { return this.model.tagParserStatus.ValueChanged; }
    public get ActiveConfigChanged(): vscode.Event<string> { return this.model.activeConfigName.ValueChanged; }

    /**
     * don't use this.rootFolder directly since it can be undefined
     */
    public get RootPath(): string {
        return (this.rootFolder) ? this.rootFolder.uri.fsPath : "";
    }
    public get RootRealPath(): string {
        return this.rootRealPath;
    }
    public get RootUri(): vscode.Uri | undefined {
        return (this.rootFolder) ? this.rootFolder.uri : undefined;
    }
    public get RootFolder(): vscode.WorkspaceFolder | undefined {
        return this.rootFolder;
    }
    public get Name(): string {
        return this.getName(this.rootFolder);
    }
    public get TrackedDocuments(): Set<vscode.TextDocument> {
        return this.trackedDocuments;
    }
    public get IsTagParsing(): boolean {
        return this.model.isTagParsing.Value;
    }
    public get ReferencesCommandMode(): refs.ReferencesCommandMode {
        return this.model.referencesCommandMode.Value;
    }

    public get languageClient(): LanguageClient {
        if (!this.innerLanguageClient) {
            throw new Error("Attempting to use languageClient before initialized");
        }
        return this.innerLanguageClient;
    }

    private get configuration(): configs.CppProperties {
        if (!this.innerConfiguration) {
            throw new Error("Attempting to use configuration before initialized");
        }
        return this.innerConfiguration;
    }

    private get AdditionalEnvironment(): { [key: string]: string | string[] } {
        return { workspaceFolderBasename: this.Name, workspaceStorage: this.storagePath };
    }

    private getName(workspaceFolder?: vscode.WorkspaceFolder): string {
        return workspaceFolder ? workspaceFolder.name : "untitled";
    }

    /**
     * All public methods on this class must be guarded by the "pendingTask" promise. Requests and notifications received before the task is
     * complete are executed after this promise is resolved.
     * @see requestWhenReady<T>(request)
     * @see notifyWhenLanguageClientReady(notify)
     * @see awaitUntilLanguageClientReady()
     */

    constructor(allClients: ClientCollection, workspaceFolder?: vscode.WorkspaceFolder) {
        this.rootFolder = workspaceFolder;
        this.rootRealPath = this.RootPath ? (fs.existsSync(this.RootPath) ? fs.realpathSync(this.RootPath) : this.RootPath) : "";
        let storagePath: string | undefined;
        if (util.extensionContext) {
            const path: string | undefined = util.extensionContext.storageUri?.fsPath;
            if (path) {
                storagePath = path;
            }
        }

        if (!storagePath) {
            storagePath = this.RootPath ? path.join(this.RootPath, "/.vscode") : "";
        }
        if (workspaceFolder && vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders.length > 1) {
            storagePath = path.join(storagePath, util.getUniqueWorkspaceStorageName(workspaceFolder));
        }
        this.storagePath = storagePath;
        const rootUri: vscode.Uri | undefined = this.RootUri;
        this.settingsTracker = getTracker(rootUri);
        try {
            let firstClient: boolean = false;
            if (!languageClient || languageClientCrashedNeedsRestart) {
                if (languageClientCrashedNeedsRestart) {
                    languageClientCrashedNeedsRestart = false;
                }
                languageClient = this.createLanguageClient(allClients);
                clientCollection = allClients;
                languageClient.registerProposedFeatures();
                languageClient.start();  // This returns Disposable, but doesn't need to be tracked because we call .stop() explicitly in our dispose()
                util.setProgress(util.getProgressExecutableStarted());
                firstClient = true;
            }
            ui = getUI();
            ui.bind(this);

            // requests/notifications are deferred until this.languageClient is set.
            this.queueBlockingTask(async () => {
                await languageClient.onReady();
                try {
                    const workspaceFolder: vscode.WorkspaceFolder | undefined = this.rootFolder;
                    this.innerConfiguration = new configs.CppProperties(rootUri, workspaceFolder);
                    this.innerConfiguration.ConfigurationsChanged((e) => this.onConfigurationsChanged(e));
                    this.innerConfiguration.SelectionChanged((e) => this.onSelectedConfigurationChanged(e));
                    this.innerConfiguration.CompileCommandsChanged((e) => this.onCompileCommandsChanged(e));
                    this.disposables.push(this.innerConfiguration);

                    this.innerLanguageClient = languageClient;
                    telemetry.logLanguageServerEvent("NonDefaultInitialCppSettings", this.settingsTracker.getUserModifiedSettings());
                    failureMessageShown = false;

                    class CodeActionProvider implements vscode.CodeActionProvider {
                        private client: DefaultClient;
                        constructor(client: DefaultClient) {
                            this.client = client;
                        }

                        public async provideCodeActions(document: vscode.TextDocument, range: vscode.Range | vscode.Selection, context: vscode.CodeActionContext, token: vscode.CancellationToken): Promise<(vscode.Command | vscode.CodeAction)[]> {
                            return this.client.requestWhenReady(async () => {
                                let r: Range;
                                if (range instanceof vscode.Selection) {
                                    if (range.active.isBefore(range.anchor)) {
                                        r = Range.create(Position.create(range.active.line, range.active.character), Position.create(range.anchor.line, range.anchor.character));
                                    } else {
                                        r = Range.create(Position.create(range.anchor.line, range.anchor.character), Position.create(range.active.line, range.active.character));
                                    }
                                } else {
                                    r = Range.create(Position.create(range.start.line, range.start.character), Position.create(range.end.line, range.end.character));
                                }

                                const params: GetCodeActionsRequestParams = {
                                    range: r,
                                    uri: document.uri.toString()
                                };

                                const commands: CodeActionCommand[] = await this.client.languageClient.sendRequest(GetCodeActionsRequest, params);
                                const resultCodeActions: vscode.CodeAction[] = [];

                                // Convert to vscode.CodeAction array
                                commands.forEach((command) => {
                                    const title: string = util.getLocalizedString(command.localizeStringParams);
                                    let edit: vscode.WorkspaceEdit | undefined;
                                    if (command.edit) {
                                        edit = new vscode.WorkspaceEdit();
                                        edit.replace(document.uri, new vscode.Range(
                                            new vscode.Position(command.edit.range.start.line, command.edit.range.start.character),
                                            new vscode.Position(command.edit.range.end.line, command.edit.range.end.character)),
                                        command.edit.newText);
                                    }
                                    const vscodeCodeAction: vscode.CodeAction = {
                                        title: title,
                                        command: command.command === "edit" ? undefined : {
                                            title: title,
                                            command: command.command,
                                            arguments: command.arguments
                                        },
                                        edit: edit,
                                        kind: edit === undefined ? vscode.CodeActionKind.QuickFix : vscode.CodeActionKind.RefactorInline
                                    };
                                    resultCodeActions.push(vscodeCodeAction);
                                });

                                return resultCodeActions;
                            });
                        }
                    }

                    // Semantic token types are identified by indexes in this list of types, in the legend.
                    const tokenTypesLegend: string[] = [];
                    for (const e in SemanticTokenTypes) {
                        // An enum is actually a set of mappings from key <=> value.  Enumerate over only the names.
                        // This allow us to represent the constants using an enum, which we can match in native code.
                        if (isNaN(Number(e))) {
                            tokenTypesLegend.push(e);
                        }
                    }
                    // Semantic token modifiers are bit indexes corresponding to the indexes in this list of modifiers in the legend.
                    const tokenModifiersLegend: string[] = [];
                    for (const e in SemanticTokenModifiers) {
                        if (isNaN(Number(e))) {
                            tokenModifiersLegend.push(e);
                        }
                    }
                    this.semanticTokensLegend = new vscode.SemanticTokensLegend(tokenTypesLegend, tokenModifiersLegend);

                    if (firstClient) {
                        workspaceReferences = new refs.ReferencesManager(this);

                        // The configurations will not be sent to the language server until the default include paths and frameworks have been set.
                        // The event handlers must be set before this happens.
                        const inputCompilerDefaults: configs.CompilerDefaults = await languageClient.sendRequest(QueryCompilerDefaultsRequest, {});
                        compilerDefaults = inputCompilerDefaults;
                        this.configuration.CompilerDefaults = compilerDefaults;

                        // Only register file watchers, providers, and the real commands after the extension has finished initializing,
                        // e.g. prevents empty c_cpp_properties.json from generation.
                        registerCommands();

                        this.registerFileWatcher();

                        this.disposables.push(vscode.languages.registerRenameProvider(this.documentSelector, new RenameProvider(this)));
                        this.disposables.push(vscode.languages.registerReferenceProvider(this.documentSelector, new FindAllReferencesProvider(this)));
                        this.disposables.push(vscode.languages.registerWorkspaceSymbolProvider(new WorkspaceSymbolProvider(this)));
                        this.disposables.push(vscode.languages.registerDocumentSymbolProvider(this.documentSelector, new DocumentSymbolProvider(this), undefined));
                        this.disposables.push(vscode.languages.registerCodeActionsProvider(this.documentSelector, new CodeActionProvider(this), undefined));
                        const settings: CppSettings = new CppSettings();
                        if (settings.formattingEngine !== "Disabled") {
                            this.documentFormattingProviderDisposable = vscode.languages.registerDocumentFormattingEditProvider(this.documentSelector, new DocumentFormattingEditProvider(this));
                            this.formattingRangeProviderDisposable = vscode.languages.registerDocumentRangeFormattingEditProvider(this.documentSelector, new DocumentRangeFormattingEditProvider(this));
                            this.onTypeFormattingProviderDisposable = vscode.languages.registerOnTypeFormattingEditProvider(this.documentSelector, new OnTypeFormattingEditProvider(this), ";", "}", "\n");
                        }
                        if (settings.codeFolding) {
                            this.codeFoldingProvider = new FoldingRangeProvider(this);
                            this.codeFoldingProviderDisposable = vscode.languages.registerFoldingRangeProvider(this.documentSelector, this.codeFoldingProvider);
                        }
                        if (settings.enhancedColorization && this.semanticTokensLegend) {
                            this.semanticTokensProvider = new SemanticTokensProvider(this);
                            this.semanticTokensProviderDisposable = vscode.languages.registerDocumentSemanticTokensProvider(this.documentSelector, this.semanticTokensProvider, this.semanticTokensLegend);
                        }
                        // Listen for messages from the language server.
                        this.registerNotifications();
                    } else {
                        this.configuration.CompilerDefaults = compilerDefaults;
                    }
                } catch (err) {
                    this.isSupported = false;   // Running on an OS we don't support yet.
                    if (!failureMessageShown) {
                        failureMessageShown = true;
                        vscode.window.showErrorMessage(localize("unable.to.start", "Unable to start the C/C++ language server. IntelliSense features will be disabled. Error: {0}", String(err)));
                    }
                }
            });
        } catch (err) {
            this.isSupported = false;   // Running on an OS we don't support yet.
            if (!failureMessageShown) {
                failureMessageShown = true;
                let additionalInfo: string;
                if (err.code === "EPERM") {
                    additionalInfo = localize('check.permissions', "EPERM: Check permissions for '{0}'", getLanguageServerFileName());
                } else {
                    additionalInfo = String(err);
                }
                vscode.window.showErrorMessage(localize("unable.to.start", "Unable to start the C/C++ language server. IntelliSense features will be disabled. Error: {0}", additionalInfo));
            }
        }
    }

    public sendFindAllReferencesNotification(params: FindAllReferencesParams): void {
        this.languageClient.sendNotification(FindAllReferencesNotification, params);
    }

    public sendRenameNofication(params: RenameParams): void {
        this.languageClient.sendNotification(RenameNotification, params);
    }

    private createLanguageClient(allClients: ClientCollection): LanguageClient {
        const serverModule: string = getLanguageServerFileName();
        const exeExists: boolean = fs.existsSync(serverModule);
        if (!exeExists) {
            telemetry.logLanguageServerEvent("missingLanguageServerBinary");
            throw String('Missing binary at ' + serverModule);
        }
        const serverName: string = this.getName(this.rootFolder);
        const serverOptions: ServerOptions = {
            run: { command: serverModule },
            debug: { command: serverModule, args: [serverName] }
        };

        // Get all the per-workspace settings.
        // They're sent as individual arrays to make it easier to process on the server,
        // so don't refactor this to an array of settings objects unless a good method is
        // found for processing data in that format on the server.
        const settings_clangFormatPath: (string | undefined)[] = [];
        const settings_clangFormatStyle: (string | undefined)[] = [];
        const settings_clangFormatFallbackStyle: (string | undefined)[] = [];
        const settings_clangFormatSortIncludes: (string | undefined)[] = [];
        const settings_filesEncoding: (string | undefined)[] = [];
        const settings_cppFilesExclude: (vscode.WorkspaceConfiguration | undefined)[] = [];
        const settings_filesExclude: (vscode.WorkspaceConfiguration | undefined)[] = [];
        const settings_searchExclude: (vscode.WorkspaceConfiguration | undefined)[] = [];
        const settings_editorAutoClosingBrackets: (string | undefined)[] = [];
        const settings_intelliSenseEngine: (string | undefined)[] = [];
        const settings_intelliSenseEngineFallback: (string | undefined)[] = [];
        const settings_errorSquiggles: (string | undefined)[] = [];
        const settings_dimInactiveRegions: boolean[] = [];
        const settings_enhancedColorization: string[] = [];
        const settings_suggestSnippets: (boolean | undefined)[] = [];
        const settings_exclusionPolicy: (string | undefined)[] = [];
        const settings_preferredPathSeparator: (string | undefined)[] = [];
        const settings_defaultSystemIncludePath: (string[] | undefined)[] = [];
        const settings_intelliSenseCachePath: (string | undefined)[] = [];
        const settings_intelliSenseCacheSize: (number | undefined)[] = [];
        const settings_intelliSenseMemoryLimit: (number | undefined)[] = [];
        const settings_autocomplete: (string | undefined)[] = [];
        const settings_autocompleteAddParentheses: (boolean | undefined)[] = [];
        const workspaceSettings: CppSettings = new CppSettings();
        const workspaceOtherSettings: OtherSettings = new OtherSettings();
        const settings_indentBraces: boolean[] = [];
        const settings_indentMultiLine: (string | undefined)[] = [];
        const settings_indentWithinParentheses: (string | undefined)[] = [];
        const settings_indentPreserveWithinParentheses: boolean[] = [];
        const settings_indentCaseLabels: boolean[] = [];
        const settings_indentCaseContents: boolean[] = [];
        const settings_indentCaseContentsWhenBlock: boolean[] = [];
        const settings_indentLambdaBracesWhenParameter: boolean[] = [];
        const settings_indentGotoLabels: (string | undefined)[] = [];
        const settings_indentPreprocessor: (string | undefined)[] = [];
        const settings_indentAccessSpecifiers: boolean[] = [];
        const settings_indentNamespaceContents: boolean[] = [];
        const settings_indentPreserveComments: boolean[] = [];
        const settings_formattingEngine: (string | undefined)[] = [];
        const settings_newLineBeforeOpenBraceNamespace: (string | undefined)[] = [];
        const settings_newLineBeforeOpenBraceType: (string | undefined)[] = [];
        const settings_newLineBeforeOpenBraceFunction: (string | undefined)[] = [];
        const settings_newLineBeforeOpenBraceBlock: (string | undefined)[] = [];
        const settings_newLineBeforeOpenBraceLambda: (string | undefined)[] = [];
        const settings_newLineScopeBracesOnSeparateLines: boolean[] = [];
        const settings_newLineCloseBraceSameLineEmptyType: boolean[] = [];
        const settings_newLineCloseBraceSameLineEmptyFunction: boolean[] = [];
        const settings_newLineBeforeCatch: boolean[] = [];
        const settings_newLineBeforeElse: boolean[] = [];
        const settings_newLineBeforeWhileInDoWhile: boolean[] = [];
        const settings_spaceBeforeFunctionOpenParenthesis: (string | undefined)[] = [];
        const settings_spaceWithinParameterListParentheses: boolean[] = [];
        const settings_spaceBetweenEmptyParameterListParentheses: boolean[] = [];
        const settings_spaceAfterKeywordsInControlFlowStatements: boolean[] = [];
        const settings_spaceWithinControlFlowStatementParentheses: boolean[] = [];
        const settings_spaceBeforeLambdaOpenParenthesis: boolean[] = [];
        const settings_spaceWithinCastParentheses: boolean[] = [];
        const settings_spaceSpaceAfterCastCloseParenthesis: boolean[] = [];
        const settings_spaceWithinExpressionParentheses: boolean[] = [];
        const settings_spaceBeforeBlockOpenBrace: boolean[] = [];
        const settings_spaceBetweenEmptyBraces: boolean[] = [];
        const settings_spaceBeforeInitializerListOpenBrace: boolean[] = [];
        const settings_spaceWithinInitializerListBraces: boolean[] = [];
        const settings_spacePreserveInInitializerList: boolean[] = [];
        const settings_spaceBeforeOpenSquareBracket: boolean[] = [];
        const settings_spaceWithinSquareBrackets: boolean[] = [];
        const settings_spaceBeforeEmptySquareBrackets: boolean[] = [];
        const settings_spaceBetweenEmptySquareBrackets: boolean[] = [];
        const settings_spaceGroupSquareBrackets: boolean[] = [];
        const settings_spaceWithinLambdaBrackets: boolean[] = [];
        const settings_spaceBetweenEmptyLambdaBrackets: boolean[] = [];
        const settings_spaceBeforeComma: boolean[] = [];
        const settings_spaceAfterComma: boolean[] = [];
        const settings_spaceRemoveAroundMemberOperators: boolean[] = [];
        const settings_spaceBeforeInheritanceColon: boolean[] = [];
        const settings_spaceBeforeConstructorColon: boolean[] = [];
        const settings_spaceRemoveBeforeSemicolon: boolean[] = [];
        const settings_spaceInsertAfterSemicolon: boolean[] = [];
        const settings_spaceRemoveAroundUnaryOperator: boolean[] = [];
        const settings_spaceAroundBinaryOperator: (string | undefined)[] = [];
        const settings_spaceAroundAssignmentOperator: (string | undefined)[] = [];
        const settings_spacePointerReferenceAlignment: (string | undefined)[] = [];
        const settings_spaceAroundTernaryOperator: (string | undefined)[] = [];
        const settings_wrapPreserveBlocks: (string | undefined)[] = [];

        {
            const settings: CppSettings[] = [];
            const otherSettings: OtherSettings[] = [];

            if (vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders.length > 0) {
                for (const workspaceFolder of vscode.workspace.workspaceFolders) {
                    settings.push(new CppSettings(workspaceFolder.uri));
                    otherSettings.push(new OtherSettings(workspaceFolder.uri));
                }
            } else {
                settings.push(workspaceSettings);
                otherSettings.push(workspaceOtherSettings);
            }

            for (const setting of settings) {
                settings_clangFormatPath.push(util.resolveVariables(setting.clangFormatPath, this.AdditionalEnvironment));
                settings_formattingEngine.push(setting.formattingEngine);
                settings_indentBraces.push(setting.vcFormatIndentBraces);
                settings_indentWithinParentheses.push(setting.vcFormatIndentWithinParentheses);
                settings_indentPreserveWithinParentheses.push(setting.vcFormatIndentPreserveWithinParentheses);
                settings_indentMultiLine.push(setting.vcFormatIndentMultiLineRelativeTo);
                settings_indentCaseLabels.push(setting.vcFormatIndentCaseLabels);
                settings_indentCaseContents.push(setting.vcFormatIndentCaseContents);
                settings_indentCaseContentsWhenBlock.push(setting.vcFormatIndentCaseContentsWhenBlock);
                settings_indentLambdaBracesWhenParameter.push(setting.vcFormatIndentLambdaBracesWhenParameter);
                settings_indentGotoLabels.push(setting.vcFormatIndentGotoLables);
                settings_indentPreprocessor.push(setting.vcFormatIndentPreprocessor);
                settings_indentAccessSpecifiers.push(setting.vcFormatIndentAccessSpecifiers);
                settings_indentNamespaceContents.push(setting.vcFormatIndentNamespaceContents);
                settings_indentPreserveComments.push(setting.vcFormatIndentPreserveComments);
                settings_newLineBeforeOpenBraceNamespace.push(setting.vcFormatNewlineBeforeOpenBraceNamespace);
                settings_newLineBeforeOpenBraceType.push(setting.vcFormatNewlineBeforeOpenBraceType);
                settings_newLineBeforeOpenBraceFunction.push(setting.vcFormatNewlineBeforeOpenBraceFunction);
                settings_newLineBeforeOpenBraceBlock.push(setting.vcFormatNewlineBeforeOpenBraceBlock);
                settings_newLineScopeBracesOnSeparateLines.push(setting.vcFormatNewlineScopeBracesOnSeparateLines);
                settings_newLineBeforeOpenBraceLambda.push(setting.vcFormatNewlineBeforeOpenBraceLambda);
                settings_newLineCloseBraceSameLineEmptyType.push(setting.vcFormatNewlineCloseBraceSameLineEmptyType);
                settings_newLineCloseBraceSameLineEmptyFunction.push(setting.vcFormatNewlineCloseBraceSameLineEmptyFunction);
                settings_newLineBeforeCatch.push(setting.vcFormatNewlineBeforeCatch);
                settings_newLineBeforeElse.push(setting.vcFormatNewlineBeforeElse);
                settings_newLineBeforeWhileInDoWhile.push(setting.vcFormatNewlineBeforeWhileInDoWhile);
                settings_spaceBeforeFunctionOpenParenthesis.push(setting.vcFormatSpaceBeforeFunctionOpenParenthesis);
                settings_spaceWithinParameterListParentheses.push(setting.vcFormatSpaceWithinParameterListParentheses);
                settings_spaceBetweenEmptyParameterListParentheses.push(setting.vcFormatSpaceBetweenEmptyParameterListParentheses);
                settings_spaceAfterKeywordsInControlFlowStatements.push(setting.vcFormatSpaceAfterKeywordsInControlFlowStatements);
                settings_spaceWithinControlFlowStatementParentheses.push(setting.vcFormatSpaceWithinControlFlowStatementParentheses);
                settings_spaceBeforeLambdaOpenParenthesis.push(setting.vcFormatSpaceBeforeLambdaOpenParenthesis);
                settings_spaceWithinCastParentheses.push(setting.vcFormatSpaceWithinCastParentheses);
                settings_spaceSpaceAfterCastCloseParenthesis.push(setting.vcFormatSpaceAfterCastCloseParenthesis);
                settings_spaceWithinExpressionParentheses.push(setting.vcFormatSpaceWithinExpressionParentheses);
                settings_spaceBeforeBlockOpenBrace.push(setting.vcFormatSpaceBeforeBlockOpenBrace);
                settings_spaceBetweenEmptyBraces.push(setting.vcFormatSpaceBetweenEmptyBraces);
                settings_spaceBeforeInitializerListOpenBrace.push(setting.vcFormatSpaceBeforeInitializerListOpenBrace);
                settings_spaceWithinInitializerListBraces.push(setting.vcFormatSpaceWithinInitializerListBraces);
                settings_spacePreserveInInitializerList.push(setting.vcFormatSpacePreserveInInitializerList);
                settings_spaceBeforeOpenSquareBracket.push(setting.vcFormatSpaceBeforeOpenSquareBracket);
                settings_spaceWithinSquareBrackets.push(setting.vcFormatSpaceWithinSquareBrackets);
                settings_spaceBeforeEmptySquareBrackets.push(setting.vcFormatSpaceBeforeEmptySquareBrackets);
                settings_spaceBetweenEmptySquareBrackets.push(setting.vcFormatSpaceBetweenEmptySquareBrackets);
                settings_spaceGroupSquareBrackets.push(setting.vcFormatSpaceGroupSquareBrackets);
                settings_spaceWithinLambdaBrackets.push(setting.vcFormatSpaceWithinLambdaBrackets);
                settings_spaceBetweenEmptyLambdaBrackets.push(setting.vcFormatSpaceBetweenEmptyLambdaBrackets);
                settings_spaceBeforeComma.push(setting.vcFormatSpaceBeforeComma);
                settings_spaceAfterComma.push(setting.vcFormatSpaceAfterComma);
                settings_spaceRemoveAroundMemberOperators.push(setting.vcFormatSpaceRemoveAroundMemberOperators);
                settings_spaceBeforeInheritanceColon.push(setting.vcFormatSpaceBeforeInheritanceColon);
                settings_spaceBeforeConstructorColon.push(setting.vcFormatSpaceBeforeConstructorColon);
                settings_spaceRemoveBeforeSemicolon.push(setting.vcFormatSpaceRemoveBeforeSemicolon);
                settings_spaceInsertAfterSemicolon.push(setting.vcFormatSpaceInsertAfterSemicolon);
                settings_spaceRemoveAroundUnaryOperator.push(setting.vcFormatSpaceRemoveAroundUnaryOperator);
                settings_spaceAroundBinaryOperator.push(setting.vcFormatSpaceAroundBinaryOperator);
                settings_spaceAroundAssignmentOperator.push(setting.vcFormatSpaceAroundAssignmentOperator);
                settings_spacePointerReferenceAlignment.push(setting.vcFormatSpacePointerReferenceAlignment);
                settings_spaceAroundTernaryOperator.push(setting.vcFormatSpaceAroundTernaryOperator);
                settings_wrapPreserveBlocks.push(setting.vcFormatWrapPreserveBlocks);
                settings_clangFormatStyle.push(setting.clangFormatStyle);
                settings_clangFormatFallbackStyle.push(setting.clangFormatFallbackStyle);
                settings_clangFormatSortIncludes.push(setting.clangFormatSortIncludes);
                settings_intelliSenseEngine.push(setting.intelliSenseEngine);
                settings_intelliSenseEngineFallback.push(setting.intelliSenseEngineFallback);
                settings_errorSquiggles.push(setting.errorSquiggles);
                settings_dimInactiveRegions.push(setting.dimInactiveRegions);
                settings_enhancedColorization.push(setting.enhancedColorization ? "Enabled" : "Disabled");
                settings_suggestSnippets.push(setting.suggestSnippets);
                settings_exclusionPolicy.push(setting.exclusionPolicy);
                settings_preferredPathSeparator.push(setting.preferredPathSeparator);
                settings_defaultSystemIncludePath.push(setting.defaultSystemIncludePath);
                settings_intelliSenseCachePath.push(util.resolveCachePath(setting.intelliSenseCachePath, this.AdditionalEnvironment));
                settings_intelliSenseCacheSize.push(setting.intelliSenseCacheSize);
                settings_intelliSenseMemoryLimit.push(setting.intelliSenseMemoryLimit);
                settings_autocomplete.push(setting.autocomplete);
                settings_autocompleteAddParentheses.push(setting.autocompleteAddParentheses);
                settings_cppFilesExclude.push(setting.filesExclude);
            }

            for (const otherSetting of otherSettings) {
                settings_filesEncoding.push(otherSetting.filesEncoding);
                settings_filesExclude.push(otherSetting.filesExclude);
                settings_searchExclude.push(otherSetting.searchExclude);
                settings_editorAutoClosingBrackets.push(otherSetting.editorAutoClosingBrackets);
            }
        }

        let intelliSenseCacheDisabled: boolean = false;
        if (os.platform() === "darwin") {
            const releaseParts: string[] = os.release().split(".");
            if (releaseParts.length >= 1) {
                // AutoPCH doesn't work for older Mac OS's.
                intelliSenseCacheDisabled = parseInt(releaseParts[0]) < 17;
            }
        }

        const localizedStrings: string[] = [];
        for (let i: number = 0; i < localizedStringCount; i++) {
            localizedStrings.push(lookupString(i));
        }

        const clientOptions: LanguageClientOptions = {
            documentSelector: [
                { scheme: 'file', language: 'c' },
                { scheme: 'file', language: 'cpp' },
                { scheme: 'file', language: 'cuda-cpp' }
            ],
            initializationOptions: {
                clang_format_path: settings_clangFormatPath,
                clang_format_style: settings_clangFormatStyle,
                formatting: settings_formattingEngine,
                vcFormat: {
                    indent: {
                        braces: settings_indentBraces,
                        multiLineRelativeTo: settings_indentMultiLine,
                        withinParentheses: settings_indentWithinParentheses,
                        preserveWithinParentheses: settings_indentPreserveWithinParentheses,
                        caseLabels: settings_indentCaseLabels,
                        caseContents: settings_indentCaseContents,
                        caseContentsWhenBlock: settings_indentCaseContentsWhenBlock,
                        lambdaBracesWhenParameter: settings_indentLambdaBracesWhenParameter,
                        gotoLabels: settings_indentGotoLabels,
                        preprocessor: settings_indentPreprocessor,
                        accesSpecifiers: settings_indentAccessSpecifiers,
                        namespaceContents: settings_indentNamespaceContents,
                        preserveComments: settings_indentPreserveComments
                    },
                    newLine: {
                        beforeOpenBrace: {
                            namespace: settings_newLineBeforeOpenBraceNamespace,
                            type: settings_newLineBeforeOpenBraceType,
                            function: settings_newLineBeforeOpenBraceFunction,
                            block: settings_newLineBeforeOpenBraceBlock,
                            lambda: settings_newLineBeforeOpenBraceLambda
                        },
                        scopeBracesOnSeparateLines: settings_newLineScopeBracesOnSeparateLines,
                        closeBraceSameLine: {
                            emptyType: settings_newLineCloseBraceSameLineEmptyType,
                            emptyFunction: settings_newLineCloseBraceSameLineEmptyFunction
                        },
                        beforeCatch: settings_newLineBeforeCatch,
                        beforeElse: settings_newLineBeforeElse,
                        beforeWhileInDoWhile: settings_newLineBeforeWhileInDoWhile

                    },
                    space: {
                        beforeFunctionOpenParenthesis: settings_spaceBeforeFunctionOpenParenthesis,
                        withinParameterListParentheses: settings_spaceWithinParameterListParentheses,
                        betweenEmptyParameterListParentheses: settings_spaceBetweenEmptyParameterListParentheses,
                        afterKeywordsInControlFlowStatements: settings_spaceAfterKeywordsInControlFlowStatements,
                        withinControlFlowStatementParentheses: settings_spaceWithinControlFlowStatementParentheses,
                        beforeLambdaOpenParenthesis: settings_spaceBeforeLambdaOpenParenthesis,
                        withinCastParentheses: settings_spaceWithinCastParentheses,
                        afterCastCloseParenthesis: settings_spaceSpaceAfterCastCloseParenthesis,
                        withinExpressionParentheses: settings_spaceWithinExpressionParentheses,
                        beforeBlockOpenBrace: settings_spaceBeforeBlockOpenBrace,
                        betweenEmptyBraces: settings_spaceBetweenEmptyBraces,
                        beforeInitializerListOpenBrace: settings_spaceBeforeInitializerListOpenBrace,
                        withinInitializerListBraces: settings_spaceWithinInitializerListBraces,
                        preserveInInitializerList: settings_spacePreserveInInitializerList,
                        beforeOpenSquareBracket: settings_spaceBeforeOpenSquareBracket,
                        withinSquareBrackets: settings_spaceWithinSquareBrackets,
                        beforeEmptySquareBrackets: settings_spaceBeforeEmptySquareBrackets,
                        betweenEmptySquareBrackets: settings_spaceBetweenEmptySquareBrackets,
                        groupSquareBrackets: settings_spaceGroupSquareBrackets,
                        withinLambdaBrackets: settings_spaceWithinLambdaBrackets,
                        betweenEmptyLambdaBrackets: settings_spaceBetweenEmptyLambdaBrackets,
                        beforeComma: settings_spaceBeforeComma,
                        afterComma: settings_spaceAfterComma,
                        removeAroundMemberOperators: settings_spaceRemoveAroundMemberOperators,
                        beforeInheritanceColon: settings_spaceBeforeInheritanceColon,
                        beforeConstructorColon: settings_spaceBeforeConstructorColon,
                        removeBeforeSemicolon: settings_spaceRemoveBeforeSemicolon,
                        insertAfterSemicolon: settings_spaceInsertAfterSemicolon,
                        removeAroundUnaryOperator: settings_spaceRemoveAroundUnaryOperator,
                        aroundBinaryOperator: settings_spaceAroundBinaryOperator,
                        aroundAssignmentOperator: settings_spaceAroundAssignmentOperator,
                        pointerReferenceAlignment: settings_spacePointerReferenceAlignment,
                        aroundTernaryOperator: settings_spaceAroundTernaryOperator
                    },
                    wrap: {
                        preserveBlocks: settings_wrapPreserveBlocks
                    }
                },
                clang_format_fallbackStyle: settings_clangFormatFallbackStyle,
                clang_format_sortIncludes: settings_clangFormatSortIncludes,
                extension_path: util.extensionPath,
                files: {
                    encoding: settings_filesEncoding
                },
                editor: {
                    autoClosingBrackets: settings_editorAutoClosingBrackets
                },
                workspace_fallback_encoding: workspaceOtherSettings.filesEncoding,
                cpp_exclude_files: settings_cppFilesExclude,
                exclude_files: settings_filesExclude,
                exclude_search: settings_searchExclude,
                associations: workspaceOtherSettings.filesAssociations,
                storage_path: this.storagePath,
                intelliSenseEngine: settings_intelliSenseEngine,
                intelliSenseEngineFallback: settings_intelliSenseEngineFallback,
                intelliSenseCacheDisabled: intelliSenseCacheDisabled,
                intelliSenseCachePath: settings_intelliSenseCachePath,
                intelliSenseCacheSize: settings_intelliSenseCacheSize,
                intelliSenseMemoryLimit: settings_intelliSenseMemoryLimit,
                intelliSenseUpdateDelay: workspaceSettings.intelliSenseUpdateDelay,
                autocomplete: settings_autocomplete,
                autocompleteAddParentheses: settings_autocompleteAddParentheses,
                errorSquiggles: settings_errorSquiggles,
                dimInactiveRegions: settings_dimInactiveRegions,
                enhancedColorization: settings_enhancedColorization,
                suggestSnippets: settings_suggestSnippets,
                simplifyStructuredComments: workspaceSettings.simplifyStructuredComments,
                loggingLevel: workspaceSettings.loggingLevel,
                workspaceParsingPriority: workspaceSettings.workspaceParsingPriority,
                workspaceSymbols: workspaceSettings.workspaceSymbols,
                exclusionPolicy: settings_exclusionPolicy,
                preferredPathSeparator: settings_preferredPathSeparator,
                default: {
                    systemIncludePath: settings_defaultSystemIncludePath
                },
                vcpkg_root: util.getVcpkgRoot(),
                experimentalFeatures: workspaceSettings.experimentalFeatures,
                edgeMessagesDirectory: path.join(util.getExtensionFilePath("bin"), "messages", util.getLocaleId()),
                localizedStrings: localizedStrings,
                supportCuda: util.supportCuda,
                packageVersion: util.packageJson.version
            },
            middleware: createProtocolFilter(allClients),
            errorHandler: {
                error: () => ErrorAction.Continue,
                closed: () => {
                    languageClientCrashTimes.push(Date.now());
                    languageClientCrashedNeedsRestart = true;
                    telemetry.logLanguageServerEvent("languageClientCrash");
                    if (languageClientCrashTimes.length < 5) {
                        allClients.forEach(client => { allClients.replace(client, true); });
                    } else {
                        const elapsed: number = languageClientCrashTimes[languageClientCrashTimes.length - 1] - languageClientCrashTimes[0];
                        if (elapsed <= 3 * 60 * 1000) {
                            vscode.window.showErrorMessage(localize('server.crashed2', "The language server crashed 5 times in the last 3 minutes. It will not be restarted."));
                            allClients.forEach(client => { allClients.replace(client, false); });
                        } else {
                            languageClientCrashTimes.shift();
                            allClients.forEach(client => { allClients.replace(client, true); });
                        }
                    }
                    return CloseAction.DoNotRestart;
                }
            }

            // TODO: should I set the output channel?  Does this sort output between servers?
        };

        // Create the language client
        this.loggingLevel = clientOptions.initializationOptions.loggingLevel;
        return new LanguageClient(`cpptools`, serverOptions, clientOptions);
    }

    public sendAllSettings(): void {
        const cppSettingsScoped: { [key: string]: any } = {};
        // Gather the C_Cpp settings
        {
            const cppSettingsResourceScoped: vscode.WorkspaceConfiguration = vscode.workspace.getConfiguration("C_Cpp", this.RootUri);
            const cppSettingsNonScoped: vscode.WorkspaceConfiguration = vscode.workspace.getConfiguration("C_Cpp");

            for (const key in cppSettingsResourceScoped) {
                const curSetting: any = util.packageJson.contributes.configuration.properties["C_Cpp." + key];
                if (curSetting === undefined) {
                    continue;
                }
                const settings: vscode.WorkspaceConfiguration = (curSetting.scope === "resource" || curSetting.scope === "machine-overridable") ? cppSettingsResourceScoped : cppSettingsNonScoped;
                cppSettingsScoped[key] = settings.get(key);
            }
            cppSettingsScoped["default"] = { systemIncludePath: cppSettingsResourceScoped.get("default.systemIncludePath") };
        }

        const otherSettingsFolder: OtherSettings = new OtherSettings(this.RootUri);
        const otherSettingsWorkspace: OtherSettings = new OtherSettings();

        // Unlike the LSP message, the event does not contain all settings as a payload, so we need to
        // build a new JSON object with everything we need on the native side.
        const settings: any = {
            C_Cpp: {
                ...cppSettingsScoped,
                files: {
                    exclude: vscode.workspace.getConfiguration("C_Cpp.files.exclude", this.RootUri)
                },
                vcFormat: {
                    ...vscode.workspace.getConfiguration("C_Cpp.vcFormat", this.RootUri),
                    indent: vscode.workspace.getConfiguration("C_Cpp.vcFormat.indent", this.RootUri),
                    newLine: {
                        ...vscode.workspace.getConfiguration("C_Cpp.vcFormat.newLine", this.RootUri),
                        beforeOpenBrace: vscode.workspace.getConfiguration("C_Cpp.vcFormat.newLine.beforeOpenBrace", this.RootUri),
                        closeBraceSameLine: vscode.workspace.getConfiguration("C_Cpp.vcFormat.newLine.closeBraceSameLine", this.RootUri)
                    },
                    space: vscode.workspace.getConfiguration("C_Cpp.vcFormat.space", this.RootUri),
                    wrap: vscode.workspace.getConfiguration("C_Cpp.vcFormat.wrap", this.RootUri)
                }
            },
            editor: {
                autoClosingBrackets: otherSettingsFolder.editorAutoClosingBrackets
            },
            files: {
                encoding: otherSettingsFolder.filesEncoding,
                exclude: vscode.workspace.getConfiguration("files.exclude", this.RootUri),
                associations: new OtherSettings().filesAssociations
            },
            workspace_fallback_encoding: otherSettingsWorkspace.filesEncoding,
            search: {
                exclude: vscode.workspace.getConfiguration("search.exclude", this.RootUri)
            }
        };

        this.sendDidChangeSettings(settings);
    }

    public sendDidChangeSettings(settings: any): void {
        // Send settings json to native side
        this.notifyWhenLanguageClientReady(() => {
            this.languageClient.sendNotification(DidChangeSettingsNotification, { settings, workspaceFolderUri: this.RootPath });
        });
    }

    public onDidChangeSettings(event: vscode.ConfigurationChangeEvent, isFirstClient: boolean): { [key: string]: string } {
        this.sendAllSettings();
        const changedSettings: { [key: string]: string } = this.settingsTracker.getChangedSettings();
        this.notifyWhenLanguageClientReady(() => {
            if (Object.keys(changedSettings).length > 0) {
                if (isFirstClient) {
                    if (changedSettings["commentContinuationPatterns"]) {
                        updateLanguageConfigurations();
                    }
                    if (changedSettings["loggingLevel"]) {
                        const oldLoggingLevelLogged: boolean = !!this.loggingLevel && this.loggingLevel !== "None" && this.loggingLevel !== "Error";
                        const newLoggingLevel: string | undefined = changedSettings["loggingLevel"];
                        this.loggingLevel = newLoggingLevel;
                        const newLoggingLevelLogged: boolean = !!newLoggingLevel && newLoggingLevel !== "None" && newLoggingLevel !== "Error";
                        if (oldLoggingLevelLogged || newLoggingLevelLogged) {
                            const out: logger.Logger = logger.getOutputChannelLogger();
                            out.appendLine(localize("loggingLevel.changed", "{0} has changed to: {1}", "loggingLevel", changedSettings["loggingLevel"]));
                        }
                    }
                    const settings: CppSettings = new CppSettings();
                    if (changedSettings["formatting"]) {
                        if (settings.formattingEngine !== "Disabled") {
                            // Because the setting is not a bool, changes do not always imply we need to
                            // register/unregister the providers.
                            if (!this.documentFormattingProviderDisposable) {
                                this.documentFormattingProviderDisposable = vscode.languages.registerDocumentFormattingEditProvider(this.documentSelector, new DocumentFormattingEditProvider(this));
                            }
                            if (!this.formattingRangeProviderDisposable) {
                                this.formattingRangeProviderDisposable = vscode.languages.registerDocumentRangeFormattingEditProvider(this.documentSelector, new DocumentRangeFormattingEditProvider(this));
                            }
                            if (!this.onTypeFormattingProviderDisposable) {
                                this.onTypeFormattingProviderDisposable = vscode.languages.registerOnTypeFormattingEditProvider(this.documentSelector, new OnTypeFormattingEditProvider(this), ";", "}", "\n");
                            }
                        } else {
                            if (this.documentFormattingProviderDisposable) {
                                this.documentFormattingProviderDisposable.dispose();
                                this.documentFormattingProviderDisposable = undefined;
                            }
                            if (this.formattingRangeProviderDisposable) {
                                this.formattingRangeProviderDisposable.dispose();
                                this.formattingRangeProviderDisposable = undefined;
                            }
                            if (this.onTypeFormattingProviderDisposable) {
                                this.onTypeFormattingProviderDisposable.dispose();
                                this.onTypeFormattingProviderDisposable = undefined;
                            }
                        }
                    }
                    if (changedSettings["codeFolding"]) {
                        if (settings.codeFolding) {
                            this.codeFoldingProvider = new FoldingRangeProvider(this);
                            this.codeFoldingProviderDisposable = vscode.languages.registerFoldingRangeProvider(this.documentSelector, this.codeFoldingProvider);
                        } else if (this.codeFoldingProviderDisposable) {
                            this.codeFoldingProviderDisposable.dispose();
                            this.codeFoldingProviderDisposable = undefined;
                            this.codeFoldingProvider = undefined;
                        }
                    }
                    if (changedSettings["enhancedColorization"]) {
                        if (settings.enhancedColorization && this.semanticTokensLegend) {
                            this.semanticTokensProvider = new SemanticTokensProvider(this);
                            this.semanticTokensProviderDisposable = vscode.languages.registerDocumentSemanticTokensProvider(this.documentSelector, this.semanticTokensProvider, this.semanticTokensLegend);
                        } else if (this.semanticTokensProviderDisposable) {
                            this.semanticTokensProviderDisposable.dispose();
                            this.semanticTokensProviderDisposable = undefined;
                            this.semanticTokensProvider = undefined;
                        }
                    }
                    // if addNodeAddonIncludePaths was turned on but no includes have been found yet then 1) presume that nan
                    // or node-addon-api was installed so prompt for reload.
                    if (changedSettings["addNodeAddonIncludePaths"] && settings.addNodeAddonIncludePaths && this.configuration.nodeAddonIncludesFound() === 0) {
                        util.promptForReloadWindowDueToSettingsChange();
                    }
                }
                this.configuration.onDidChangeSettings();
                telemetry.logLanguageServerEvent("CppSettingsChange", changedSettings, undefined);
            }
        });
        return changedSettings;
    }

    public onDidChangeVisibleTextEditors(editors: vscode.TextEditor[]): void {
        const settings: CppSettings = new CppSettings(this.RootUri);
        if (settings.dimInactiveRegions) {
            // Apply text decorations to inactive regions
            for (const e of editors) {
                const valuePair: DecorationRangesPair | undefined = this.inactiveRegionsDecorations.get(e.document.uri.toString());
                if (valuePair) {
                    e.setDecorations(valuePair.decoration, valuePair.ranges); // VSCode clears the decorations when the text editor becomes invisible
                }
            }
        }
    }

    public onDidChangeTextDocument(textDocumentChangeEvent: vscode.TextDocumentChangeEvent): void {
        if (textDocumentChangeEvent.document.uri.scheme === "file") {
            if (textDocumentChangeEvent.document.languageId === "c"
                || textDocumentChangeEvent.document.languageId === "cpp"
                || textDocumentChangeEvent.document.languageId === "cuda-cpp") {
                // If any file has changed, we need to abort the current rename operation
                if (DefaultClient.renamePending) {
                    this.cancelReferences();
                }

                const oldVersion: number | undefined = openFileVersions.get(textDocumentChangeEvent.document.uri.toString());
                const newVersion: number = textDocumentChangeEvent.document.version;
                if (oldVersion === undefined || newVersion > oldVersion) {
                    openFileVersions.set(textDocumentChangeEvent.document.uri.toString(), newVersion);
                }
            }
        }
    }

    public onDidOpenTextDocument(document: vscode.TextDocument): void {
        if (document.uri.scheme === "file") {
            openFileVersions.set(document.uri.toString(), document.version);
        }
    }

    public onDidCloseTextDocument(document: vscode.TextDocument): void {
        if (this.semanticTokensProvider) {
            this.semanticTokensProvider.invalidateFile(document.uri.toString());
        }
        openFileVersions.delete(document.uri.toString());
    }

    private registeredProviders: CustomConfigurationProvider1[] = [];
    public onRegisterCustomConfigurationProvider(provider: CustomConfigurationProvider1): Thenable<void> {
        const onRegistered: () => void = () => {
            // version 2 providers control the browse.path. Avoid thrashing the tag parser database by pausing parsing until
            // the provider has sent the correct browse.path value.
            if (provider.version >= Version.v2) {
                this.pauseParsing();
            }
        };
        return this.notifyWhenLanguageClientReady(() => {
            if (this.registeredProviders.includes(provider)) {
                return; // Prevent duplicate processing.
            }
            this.registeredProviders.push(provider);
            const rootFolder: vscode.WorkspaceFolder | undefined = this.RootFolder;
            if (!rootFolder) {
                return; // There is no c_cpp_properties.json to edit because there is no folder open.
            }
            this.configuration.handleConfigurationChange();
            const selectedProvider: string | undefined = this.configuration.CurrentConfigurationProvider;
            if (!selectedProvider) {
                const ask: PersistentFolderState<boolean> = new PersistentFolderState<boolean>("Client.registerProvider", true, rootFolder);
                // If c_cpp_properties.json and settings.json are both missing, reset our prompt
                if (!fs.existsSync(`${this.RootPath}/.vscode/c_cpp_properties.json`) && !fs.existsSync(`${this.RootPath}/.vscode/settings.json`)) {
                    ask.Value = true;
                }
                if (ask.Value) {
                    ui.showConfigureCustomProviderMessage(async () => {
                        const message: string = (vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders.length > 1)
                            ? localize("provider.configure.folder", "{0} would like to configure IntelliSense for the '{1}' folder.", provider.name, this.Name)
                            : localize("provider.configure.this.folder", "{0} would like to configure IntelliSense for this folder.", provider.name);
                        const allow: string = localize("allow.button", "Allow");
                        const dontAllow: string = localize("dont.allow.button", "Don't Allow");
                        const askLater: string = localize("ask.me.later.button", "Ask Me Later");
                        return vscode.window.showInformationMessage(message, allow, dontAllow, askLater).then(async result => {
                            switch (result) {
                                case allow: {
                                    await this.configuration.updateCustomConfigurationProvider(provider.extensionId);
                                    onRegistered();
                                    ask.Value = false;
                                    telemetry.logLanguageServerEvent("customConfigurationProvider", { "providerId": provider.extensionId });
                                    return true;
                                }
                                case dontAllow: {
                                    ask.Value = false;
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                            return false;
                        });
                    }, () => ask.Value = false);
                }
            } else if (isSameProviderExtensionId(selectedProvider, provider.extensionId)) {
                onRegistered();
                telemetry.logLanguageServerEvent("customConfigurationProvider", { "providerId": provider.extensionId });
            } else if (selectedProvider === provider.name) {
                onRegistered();
                this.configuration.updateCustomConfigurationProvider(provider.extensionId); // v0 -> v1 upgrade. Update the configurationProvider in c_cpp_properties.json
            }
        });
    }

    public updateCustomConfigurations(requestingProvider?: CustomConfigurationProvider1): Thenable<void> {
        return this.notifyWhenLanguageClientReady(() => {
            if (!this.configurationProvider) {
                this.clearCustomConfigurations();
                return;
            }
            const currentProvider: CustomConfigurationProvider1 | undefined = getCustomConfigProviders().get(this.configurationProvider);
            if (!currentProvider) {
                this.clearCustomConfigurations();
                return;
            }
            if (requestingProvider && requestingProvider.extensionId !== currentProvider.extensionId) {
                // If we are being called by a configuration provider other than the current one, ignore it.
                return;
            }

            this.clearCustomConfigurations();
            this.trackedDocuments.forEach(document => {
                this.provideCustomConfiguration(document.uri, undefined);
            });
        });
    }

    public updateCustomBrowseConfiguration(requestingProvider?: CustomConfigurationProvider1): Promise<void> {
        return this.notifyWhenLanguageClientReady(() => {
            if (!this.configurationProvider) {
                return;
            }
            console.log("updateCustomBrowseConfiguration");
            const currentProvider: CustomConfigurationProvider1 | undefined = getCustomConfigProviders().get(this.configurationProvider);
            if (!currentProvider || (requestingProvider && requestingProvider.extensionId !== currentProvider.extensionId)) {
                return;
            }

            const tokenSource: vscode.CancellationTokenSource = new vscode.CancellationTokenSource();
            const task: () => Thenable<WorkspaceBrowseConfiguration | null> = async () => {
                if (this.RootUri && await currentProvider.canProvideBrowseConfigurationsPerFolder(tokenSource.token)) {
                    return (currentProvider.provideFolderBrowseConfiguration(this.RootUri, tokenSource.token));
                }
                if (await currentProvider.canProvideBrowseConfiguration(tokenSource.token)) {
                    return currentProvider.provideBrowseConfiguration(tokenSource.token);
                }
                if (currentProvider.version >= Version.v2) {
                    console.warn("failed to provide browse configuration");
                }
                return null;
            };

            // Initiate request for custom configuration.
            // Resume parsing on either resolve or reject, only if parsing was not resumed due to timeout
            let hasCompleted: boolean = false;
            task().then(async config => {
                if (!config) {
                    return;
                }
                if (currentProvider.version < Version.v3) {
                    // This is to get around the (fixed) CMake Tools bug: https://github.com/microsoft/vscode-cmake-tools/issues/1073
                    for (const c of config.browsePath) {
                        if (vscode.workspace.getWorkspaceFolder(vscode.Uri.file(c)) === this.RootFolder) {
                            this.sendCustomBrowseConfiguration(config, currentProvider.extensionId);
                            break;
                        }
                    }
                } else {
                    this.sendCustomBrowseConfiguration(config, currentProvider.extensionId);
                }
                if (!hasCompleted) {
                    hasCompleted = true;
                    if (currentProvider.version >= Version.v2) {
                        this.resumeParsing();
                    }
                }
            }, () => {
                if (!hasCompleted) {
                    hasCompleted = true;
                    if (currentProvider.version >= Version.v2) {
                        this.resumeParsing();
                    }
                }
            });

            // Set up a timeout to use previously received configuration and resume parsing if the provider times out
            global.setTimeout(async () => {
                if (!hasCompleted) {
                    hasCompleted = true;
                    this.sendCustomBrowseConfiguration(null, undefined, true);
                    if (currentProvider.version >= Version.v2) {
                        console.warn("Configuration Provider timed out in {0}ms.", configProviderTimeout);
                        this.resumeParsing();
                    }
                }
            }, configProviderTimeout);
        });
    }

    public toggleReferenceResultsView(): void {
        workspaceReferences.toggleGroupView();
    }

    public async logDiagnostics(): Promise<void> {
        const response: GetDiagnosticsResult = await this.requestWhenReady(() => this.languageClient.sendRequest(GetDiagnosticsRequest, null));
        if (!diagnosticsChannel) {
            diagnosticsChannel = vscode.window.createOutputChannel(localize("c.cpp.diagnostics", "C/C++ Diagnostics"));
            workspaceDisposables.push(diagnosticsChannel);
        } else {
            diagnosticsChannel.clear();
        }

        const header: string = `-------- Diagnostics - ${new Date().toLocaleString()}\n`;
        const version: string = `Version: ${util.packageJson.version}\n`;
        let configJson: string = "";
        if (this.configuration.CurrentConfiguration) {
            configJson = `Current Configuration:\n${JSON.stringify(this.configuration.CurrentConfiguration, null, 4)}\n`;
        }

        // Get diagnotics for configuration provider info.
        let configurationLoggingStr: string = "";
        const tuSearchStart: number = response.diagnostics.indexOf("Translation Unit Mappings:");
        if (tuSearchStart >= 0) {
            const tuSearchEnd: number = response.diagnostics.indexOf("Translation Unit Configurations:");
            if (tuSearchEnd >= 0 && tuSearchEnd > tuSearchStart) {
                let tuSearchString: string = response.diagnostics.substr(tuSearchStart, tuSearchEnd - tuSearchStart);
                let tuSearchIndex: number = tuSearchString.indexOf("[");
                while (tuSearchIndex >= 0) {
                    const tuMatch: RegExpMatchArray | null = tuSearchString.match(/\[\s(.*)\s\]/);
                    if (tuMatch && tuMatch.length > 1) {
                        const tuPath: string = vscode.Uri.file(tuMatch[1]).toString();
                        if (this.configurationLogging.has(tuPath)) {
                            if (configurationLoggingStr.length === 0) {
                                configurationLoggingStr += "Custom configurations:\n";
                            }
                            configurationLoggingStr += `[ ${tuMatch[1]} ]\n${this.configurationLogging.get(tuPath)}\n`;
                        }
                    }
                    tuSearchString = tuSearchString.substr(tuSearchIndex + 1);
                    tuSearchIndex = tuSearchString.indexOf("[");
                }
            }
        }
        diagnosticsChannel.appendLine(`${header}${version}${configJson}${this.browseConfigurationLogging}${configurationLoggingStr}${response.diagnostics}`);
        diagnosticsChannel.show(false);
    }

    public async rescanFolder(): Promise<void> {
        await this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(RescanFolderNotification));
    }

    public async provideCustomConfiguration(docUri: vscode.Uri, requestFile?: string): Promise<void> {
        const onFinished: () => void = () => {
            if (requestFile) {
                this.languageClient.sendNotification(FinishedRequestCustomConfig, requestFile);
            }
        };
        const providerId: string | undefined = this.configurationProvider;
        if (!providerId) {
            onFinished();
            return;
        }
        const provider: CustomConfigurationProvider1 | undefined = getCustomConfigProviders().get(providerId);
        if (!provider) {
            onFinished();
            return;
        }
        if (!provider.isReady) {
            onFinished();
            throw new Error(`${this.configurationProvider} is not ready`);
        }
        return this.queueBlockingTask(async () => {
            const tokenSource: vscode.CancellationTokenSource = new vscode.CancellationTokenSource();
            console.log("provideCustomConfiguration");

            const providerName: string = provider.name;

            const params: QueryTranslationUnitSourceParams = {
                uri: docUri.toString(),
                workspaceFolderUri: this.RootPath
            };
            const response: QueryTranslationUnitSourceResult = await this.languageClient.sendRequest(QueryTranslationUnitSourceRequest, params);
            if (!response.candidates || response.candidates.length === 0) {
                // If we didn't receive any candidates, no configuration is needed.
                onFinished();
                return;
            }

            // Need to loop through candidates, to see if we can get a custom configuration from any of them.
            // Wrap all lookups in a single task, so we can apply a timeout to the entire duration.
            const provideConfigurationAsync: () => Thenable<SourceFileConfigurationItem[] | null | undefined> = async () => {
                if (provider) {
                    for (let i: number = 0; i < response.candidates.length; ++i) {
                        try {
                            const candidate: string = response.candidates[i];
                            const tuUri: vscode.Uri = vscode.Uri.parse(candidate);
                            if (await provider.canProvideConfiguration(tuUri, tokenSource.token)) {
                                const configs: SourceFileConfigurationItem[] = await provider.provideConfigurations([tuUri], tokenSource.token);
                                if (configs && configs.length > 0 && configs[0]) {
                                    return configs;
                                }
                            }
                            if (tokenSource.token.isCancellationRequested) {
                                return null;
                            }
                        } catch (err) {
                            console.warn("Caught exception request configuration");
                        }
                    }
                }
            };
            const configs: SourceFileConfigurationItem[] | null | undefined = await this.callTaskWithTimeout(provideConfigurationAsync, configProviderTimeout, tokenSource);
            try {
                if (configs && configs.length > 0) {
                    this.sendCustomConfigurations(configs, provider.version);
                }
                onFinished();
            } catch (err) {
                if (requestFile) {
                    onFinished();
                    return;
                }
                const settings: CppSettings = new CppSettings(this.RootUri);
                if (settings.configurationWarnings === "Enabled" && !this.isExternalHeader(docUri) && !vscode.debug.activeDebugSession) {
                    const dismiss: string = localize("dismiss.button", "Dismiss");
                    const disable: string = localize("diable.warnings.button", "Disable Warnings");
                    const configName: string | undefined = this.configuration.CurrentConfiguration?.name;
                    if (!configName) {
                        return;
                    }
                    let message: string = localize("unable.to.provide.configuration",
                        "{0} is unable to provide IntelliSense configuration information for '{1}'. Settings from the '{2}' configuration will be used instead.",
                        providerName, docUri.fsPath, configName);
                    if (err) {
                        message += ` (${err})`;
                    }

                    vscode.window.showInformationMessage(message, dismiss, disable).then(response => {
                        switch (response) {
                            case disable: {
                                settings.toggleSetting("configurationWarnings", "Enabled", "Disabled");
                                break;
                            }
                        }
                    });
                }
            }
        });
    }

    private async handleRequestCustomConfig(requestFile: string): Promise<void> {
        await this.provideCustomConfiguration(vscode.Uri.file(requestFile), requestFile);
    }

    private isExternalHeader(uri: vscode.Uri): boolean {
        const rootUri: vscode.Uri | undefined = this.RootUri;
        return !rootUri || (util.isHeader(uri) && !uri.toString().startsWith(rootUri.toString()));
    }

    public getCurrentConfigName(): Thenable<string | undefined> {
        return this.queueTask(() => Promise.resolve(this.configuration.CurrentConfiguration?.name));
    }

    public getCurrentConfigCustomVariable(variableName: string): Thenable<string> {
        return this.queueTask(() => Promise.resolve(this.configuration.CurrentConfiguration?.customConfigurationVariables?.[variableName] || ''));
    }

    public setCurrentConfigName(configurationName: string): Thenable<void> {
        return this.queueTask(() => new Promise((resolve, reject) => {
            const configurations: configs.Configuration[] = this.configuration.Configurations || [];
            const configurationIndex: number = configurations.findIndex((config) => config.name === configurationName);

            if (configurationIndex !== -1) {
                this.configuration.select(configurationIndex);
                resolve();
            } else {
                reject(new Error(localize("config.not.found", "The requested configuration name is not found: {0}", configurationName)));
            }
        }));
    }

    public getCurrentCompilerPathAndArgs(): Thenable<util.CompilerPathAndArgs | undefined> {
        return this.queueTask(() => Promise.resolve(
            util.extractCompilerPathAndArgs(
                this.configuration.CurrentConfiguration?.compilerPath,
                this.configuration.CurrentConfiguration?.compilerArgs)
        ));
    }

    public getVcpkgInstalled(): Thenable<boolean> {
        return this.queueTask(() => Promise.resolve(this.configuration.VcpkgInstalled));
    }

    public getVcpkgEnabled(): Thenable<boolean> {
        const cppSettings: CppSettings = new CppSettings(this.RootUri);
        return Promise.resolve(cppSettings.vcpkgEnabled === true);
    }

    public getKnownCompilers(): Thenable<configs.KnownCompiler[] | undefined> {
        return this.queueTask(() => Promise.resolve(this.configuration.KnownCompiler));
    }

    /**
     * Take ownership of a document that was previously serviced by another client.
     * This process involves sending a textDocument/didOpen message to the server so
     * that it knows about the file, as well as adding it to this client's set of
     * tracked documents.
     */
    public takeOwnership(document: vscode.TextDocument): void {
        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: document.uri.toString(),
                languageId: document.languageId,
                version: document.version,
                text: document.getText()
            }
        };
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(DidOpenNotification, params));
        this.trackedDocuments.add(document);
    }

    /**
     * wait until the all pendingTasks are complete (e.g. language client is ready for use)
     * before attempting to send messages or operate on the client.
     */

    public async queueTask<T>(task: () => Thenable<T>): Promise<T> {
        if (this.isSupported) {
            const nextTask: () => Promise<T> = async () => {
                try {
                    return await task();
                } catch (err) {
                    console.error(err);
                    throw err;
                }
            };
            if (pendingTask && !pendingTask.Done) {
                // We don't want the queue to stall because of a rejected promise.
                try {
                    await pendingTask.getPromise();
                } catch (e) { }
            } else {
                pendingTask = undefined;
            }
            return nextTask();
        } else {
            throw new Error(localize("unsupported.client", "Unsupported client"));
        }
    }

    /**
     * Queue a task that blocks all future tasks until it completes. This is currently only intended to be used
     * during language client startup and for custom configuration providers.
     * @param task The task that blocks all future tasks
     */
    private async queueBlockingTask<T>(task: () => Thenable<T>): Promise<T> {
        if (this.isSupported) {
            pendingTask = new util.BlockingTask<T>(task, pendingTask);
            return pendingTask.getPromise();
        } else {
            throw new Error(localize("unsupported.client", "Unsupported client"));
        }
    }

    private callTaskWithTimeout<T>(task: () => Thenable<T>, ms: number, cancelToken?: vscode.CancellationTokenSource): Promise<T> {
        let timer: NodeJS.Timer;
        // Create a promise that rejects in <ms> milliseconds
        const timeout: () => Promise<T> = () => new Promise<T>((resolve, reject) => {
            timer = global.setTimeout(() => {
                clearTimeout(timer);
                if (cancelToken) {
                    cancelToken.cancel();
                }
                reject(localize("timed.out", "Timed out in {0}ms.", ms));
            }, ms);
        });

        // Returns a race between our timeout and the passed in promise
        return Promise.race([task(), timeout()]).then(
            (result: any) => {
                clearTimeout(timer);
                return result;
            },
            (error: any) => {
                clearTimeout(timer);
                throw error;
            });
    }

    public requestWhenReady<T>(request: () => Thenable<T>): Thenable<T> {
        return this.queueTask(request);
    }

    public notifyWhenLanguageClientReady<T>(notify: () => T): Promise<T> {
        const task: () => Promise<T> = () => new Promise<T>(resolve => {
            resolve(notify());
        });
        return this.queueTask(task);
    }

    public awaitUntilLanguageClientReady(): Thenable<void> {
        const task: () => Thenable<void> = () => new Promise<void>(resolve => {
            resolve();
        });
        return this.queueTask(task);
    }

    /**
     * listen for notifications from the language server.
     */
    private registerNotifications(): void {
        console.assert(this.languageClient !== undefined, "This method must not be called until this.languageClient is set in \"onReady\"");

        this.languageClient.onNotification(ReloadWindowNotification, () => util.promptForReloadWindowDueToSettingsChange());
        this.languageClient.onNotification(LogTelemetryNotification, logTelemetry);
        this.languageClient.onNotification(ReportStatusNotification, (e) => this.updateStatus(e));
        this.languageClient.onNotification(ReportTagParseStatusNotification, (e) => this.updateTagParseStatus(e));
        this.languageClient.onNotification(InactiveRegionNotification, (e) => this.updateInactiveRegions(e));
        this.languageClient.onNotification(CompileCommandsPathsNotification, (e) => this.promptCompileCommands(e));
        this.languageClient.onNotification(ReferencesNotification, (e) => this.processReferencesResult(e.referencesResult));
        this.languageClient.onNotification(ReportReferencesProgressNotification, (e) => this.handleReferencesProgress(e));
        this.languageClient.onNotification(RequestCustomConfig, (requestFile: string) => {
            const client: DefaultClient = <DefaultClient>clientCollection.getClientFor(vscode.Uri.file(requestFile));
            client.handleRequestCustomConfig(requestFile);
        });
        this.languageClient.onNotification(PublishDiagnosticsNotification, publishDiagnostics);
        this.languageClient.onNotification(ShowMessageWindowNotification, showMessageWindow);
        this.languageClient.onNotification(ShowWarningNotification, showWarning);
        this.languageClient.onNotification(ReportTextDocumentLanguage, (e) => this.setTextDocumentLanguage(e));
        this.languageClient.onNotification(SemanticTokensChanged, (e) => this.semanticTokensProvider?.invalidateFile(e));
        this.languageClient.onNotification(IntelliSenseSetupNotification, (e) => this.logIntellisenseSetupTime(e));
        this.languageClient.onNotification(SetTemporaryTextDocumentLanguageNotification, (e) => this.setTemporaryTextDocumentLanguage(e));
        setupOutputHandlers();
    }

    private setTextDocumentLanguage(languageStr: string): void {
        const cppSettings: CppSettings = new CppSettings();
        if (cppSettings.autoAddFileAssociations) {
            const is_c: boolean = languageStr.startsWith("c;");
            const is_cuda: boolean = languageStr.startsWith("cu;");
            languageStr = languageStr.substr(is_c ? 2 : (is_cuda ? 3 : 1));
            this.addFileAssociations(languageStr, is_c ? "c" : (is_cuda ? "cuda-cpp" : "cpp"));
        }
    }

    private async setTemporaryTextDocumentLanguage(params: SetTemporaryTextDocumentLanguageParams): Promise<void> {
        const languageId: string = params.isC ? "c" : (params.isCuda ? "cuda-cpp" : "cpp");
        const document: vscode.TextDocument = await vscode.workspace.openTextDocument(params.path);
        if (!!document && document.languageId !== languageId) {
            vscode.languages.setTextDocumentLanguage(document, languageId);
        }
    }

    private associations_for_did_change?: Set<string>;

    /**
     * listen for file created/deleted events under the ${workspaceFolder} folder
     */
    private registerFileWatcher(): void {
        console.assert(this.languageClient !== undefined, "This method must not be called until this.languageClient is set in \"onReady\"");

        if (this.rootFolder) {
            // WARNING: The default limit on Linux is 8k, so for big directories, this can cause file watching to fail.
            this.rootPathFileWatcher = vscode.workspace.createFileSystemWatcher(
                "**/*",
                false /* ignoreCreateEvents */,
                false /* ignoreChangeEvents */,
                false /* ignoreDeleteEvents */);

            this.rootPathFileWatcher.onDidCreate((uri) => {
                if (path.basename(uri.fsPath).toLowerCase() === ".editorconfig") {
                    cachedEditorConfigSettings.clear();
                }

                this.languageClient.sendNotification(FileCreatedNotification, { uri: uri.toString() });
            });

            // TODO: Handle new associations without a reload.
            this.associations_for_did_change = new Set<string>(["cu", "cuh", "c", "i", "cpp", "cc", "cxx", "c++", "cp", "hpp", "hh", "hxx", "h++", "hp", "h", "ii", "ino", "inl", "ipp", "tcc", "idl"]);
            const assocs: any = new OtherSettings().filesAssociations;
            for (const assoc in assocs) {
                const dotIndex: number = assoc.lastIndexOf('.');
                if (dotIndex !== -1) {
                    const ext: string = assoc.substr(dotIndex + 1);
                    this.associations_for_did_change.add(ext);
                }
            }
            this.rootPathFileWatcher.onDidChange((uri) => {
                const dotIndex: number = uri.fsPath.lastIndexOf('.');

                if (path.basename(uri.fsPath).toLowerCase() === ".editorconfig") {
                    cachedEditorConfigSettings.clear();
                }

                if (dotIndex !== -1) {
                    const ext: string = uri.fsPath.substr(dotIndex + 1);
                    if (this.associations_for_did_change?.has(ext)) {
                        // VS Code has a bug that causes onDidChange events to happen to files that aren't changed,
                        // which causes a large backlog of "files to parse" to accumulate.
                        // We workaround this via only sending the change message if the modified time is within 10 seconds.
                        const mtime: Date = fs.statSync(uri.fsPath).mtime;
                        const duration: number = Date.now() - mtime.getTime();
                        if (duration < 10000) {
                            this.languageClient.sendNotification(FileChangedNotification, { uri: uri.toString() });
                        }
                    }
                }
            });

            this.rootPathFileWatcher.onDidDelete((uri) => {
                if (path.basename(uri.fsPath).toLowerCase() === ".editorconfig") {
                    cachedEditorConfigSettings.clear();
                }

                this.languageClient.sendNotification(FileDeletedNotification, { uri: uri.toString() });
            });

            this.disposables.push(this.rootPathFileWatcher);
        } else {
            this.rootPathFileWatcher = undefined;
        }
    }

    /**
     * handle notifications coming from the language server
     */

    public addFileAssociations(fileAssociations: string, languageId: string): void {
        const settings: OtherSettings = new OtherSettings();
        const assocs: any = settings.filesAssociations;

        const filesAndPaths: string[] = fileAssociations.split(";");
        let foundNewAssociation: boolean = false;
        for (let i: number = 0; i < filesAndPaths.length; ++i) {
            const fileAndPath: string[] = filesAndPaths[i].split("@");
            // Skip empty or malformed
            if (fileAndPath.length === 2) {
                const file: string = fileAndPath[0];
                const filePath: string = fileAndPath[1];
                if ((file in assocs) || (("**/" + file) in assocs)) {
                    continue; // File already has an association.
                }
                const j: number = file.lastIndexOf('.');
                if (j !== -1) {
                    const ext: string = file.substr(j);
                    if ((("*" + ext) in assocs) || (("**/*" + ext) in assocs)) {
                        continue; // Extension already has an association.
                    }
                }
                let foundGlobMatch: boolean = false;
                for (const assoc in assocs) {
                    if (minimatch(filePath, assoc)) {
                        foundGlobMatch = true;
                        break; // Assoc matched a glob pattern.
                    }
                }
                if (foundGlobMatch) {
                    continue;
                }
                assocs[file] = languageId;
                foundNewAssociation = true;
            }
        }
        if (foundNewAssociation) {
            settings.filesAssociations = assocs;
        }
    }

    private updateStatus(notificationBody: ReportStatusNotificationBody): void {
        const message: string = notificationBody.status;
        util.setProgress(util.getProgressExecutableSuccess());
        const testHook: TestHook = getTestHook();
        if (message.endsWith("Indexing...")) {
            this.model.isTagParsing.Value = true;
            const status: IntelliSenseStatus = { status: Status.TagParsingBegun };
            testHook.updateStatus(status);
        } else if (message.endsWith("Updating IntelliSense...")) {
            timeStamp = Date.now();
            this.model.isUpdatingIntelliSense.Value = true;
            const status: IntelliSenseStatus = { status: Status.IntelliSenseCompiling };
            testHook.updateStatus(status);
        } else if (message.endsWith("IntelliSense Ready")) {
            const settings: CppSettings = new CppSettings();
            if (settings.loggingLevel === "Debug") {
                const out: logger.Logger = logger.getOutputChannelLogger();
                const duration: number = Date.now() - timeStamp;
                out.appendLine(localize("update.intellisense.time", "Update IntelliSense time (sec): {0}", duration / 1000));
            }
            this.model.isUpdatingIntelliSense.Value = false;
            const status: IntelliSenseStatus = { status: Status.IntelliSenseReady };
            testHook.updateStatus(status);
        } else if (message.endsWith("Ready")) { // Tag Parser Ready
            this.model.isTagParsing.Value = false;
            const status: IntelliSenseStatus = { status: Status.TagParsingDone };
            testHook.updateStatus(status);
            util.setProgress(util.getProgressParseRootSuccess());
        } else if (message.includes("Squiggles Finished - File name:")) {
            const index: number = message.lastIndexOf(":");
            const name: string = message.substring(index + 2);
            const status: IntelliSenseStatus = { status: Status.IntelliSenseReady, filename: name };
            testHook.updateStatus(status);
        } else if (message.endsWith("No Squiggles")) {
            util.setIntelliSenseProgress(util.getProgressIntelliSenseNoSquiggles());
        } else if (message.endsWith("Unresolved Headers")) {
            if (notificationBody.workspaceFolderUri) {
                const client: DefaultClient = <DefaultClient>clientCollection.getClientFor(vscode.Uri.file(notificationBody.workspaceFolderUri));
                if (!client.configuration.CurrentConfiguration?.configurationProvider) {
                    const showIntelliSenseFallbackMessage: PersistentState<boolean> = new PersistentState<boolean>("CPP.showIntelliSenseFallbackMessage", true);
                    if (showIntelliSenseFallbackMessage.Value) {
                        ui.showConfigureIncludePathMessage(async () => {
                            const configJSON: string = localize("configure.json.button", "Configure (JSON)");
                            const configUI: string = localize("configure.ui.button", "Configure (UI)");
                            const dontShowAgain: string = localize("dont.show.again", "Don't Show Again");
                            const fallbackMsg: string = client.configuration.VcpkgInstalled ?
                                localize("update.your.intellisense.settings", "Update your IntelliSense settings or use Vcpkg to install libraries to help find missing headers.") :
                                localize("configure.your.intellisense.settings", "Configure your IntelliSense settings to help find missing headers.");
                            return vscode.window.showInformationMessage(fallbackMsg, configJSON, configUI, dontShowAgain).then(async (value) => {
                                let commands: string[];
                                switch (value) {
                                    case configJSON:
                                        commands = await vscode.commands.getCommands(true);
                                        if (commands.indexOf("workbench.action.problems.focus") >= 0) {
                                            vscode.commands.executeCommand("workbench.action.problems.focus");
                                        }
                                        client.handleConfigurationEditJSONCommand();
                                        telemetry.logLanguageServerEvent("SettingsCommand", { "toast": "json" }, undefined);
                                        break;
                                    case configUI:
                                        commands = await vscode.commands.getCommands(true);
                                        if (commands.indexOf("workbench.action.problems.focus") >= 0) {
                                            vscode.commands.executeCommand("workbench.action.problems.focus");
                                        }
                                        client.handleConfigurationEditUICommand();
                                        telemetry.logLanguageServerEvent("SettingsCommand", { "toast": "ui" }, undefined);
                                        break;
                                    case dontShowAgain:
                                        showIntelliSenseFallbackMessage.Value = false;
                                        break;
                                }
                                return true;
                            });
                        }, () => showIntelliSenseFallbackMessage.Value = false);
                    }
                }
            }
        }
    }

    private updateTagParseStatus(notificationBody: LocalizeStringParams): void {
        this.model.tagParserStatus.Value = util.getLocalizedString(notificationBody);
    }

    private updateInactiveRegions(params: InactiveRegionParams): void {
        const settings: CppSettings = new CppSettings(this.RootUri);
        const opacity: number | undefined = settings.inactiveRegionOpacity;
        if (opacity !== null && opacity !== undefined) {
            let backgroundColor: string | undefined = settings.inactiveRegionBackgroundColor;
            if (backgroundColor === "") {
                backgroundColor = undefined;
            }
            let color: string | undefined = settings.inactiveRegionForegroundColor;
            if (color === "") {
                color = undefined;
            }
            const decoration: vscode.TextEditorDecorationType = vscode.window.createTextEditorDecorationType({
                opacity: opacity.toString(),
                backgroundColor: backgroundColor,
                color: color,
                rangeBehavior: vscode.DecorationRangeBehavior.OpenOpen
            });
            // We must convert to vscode.Ranges in order to make use of the API's
            const ranges: vscode.Range[] = [];
            params.regions.forEach(element => {
                const newRange: vscode.Range = new vscode.Range(element.startLine, 0, element.endLine, 0);
                ranges.push(newRange);
            });
            // Find entry for cached file and act accordingly
            const valuePair: DecorationRangesPair | undefined = this.inactiveRegionsDecorations.get(params.uri);
            if (valuePair) {
                // Disposing of and resetting the decoration will undo previously applied text decorations
                valuePair.decoration.dispose();
                valuePair.decoration = decoration;
                // As vscode.TextEditor.setDecorations only applies to visible editors, we must cache the range for when another editor becomes visible
                valuePair.ranges = ranges;
            } else { // The entry does not exist. Make a new one
                const toInsert: DecorationRangesPair = {
                    decoration: decoration,
                    ranges: ranges
                };
                this.inactiveRegionsDecorations.set(params.uri, toInsert);
            }
            if (settings.dimInactiveRegions && params.fileVersion === openFileVersions.get(params.uri)) {
                // Apply the decorations to all *visible* text editors
                const editors: vscode.TextEditor[] = vscode.window.visibleTextEditors.filter(e => e.document.uri.toString() === params.uri);
                for (const e of editors) {
                    e.setDecorations(decoration, ranges);
                }
            }
        }
        if (this.codeFoldingProvider) {
            this.codeFoldingProvider.refresh();
        }
    }

    public logIntellisenseSetupTime(notification: IntelliSenseSetup): void {
        clientCollection.timeTelemetryCollector.setSetupTime(vscode.Uri.parse(notification.uri));
    }

    private promptCompileCommands(params: CompileCommandsPaths): void {
        if (!params.workspaceFolderUri) {
            return;
        }
        const client: DefaultClient = <DefaultClient>clientCollection.getClientFor(vscode.Uri.file(params.workspaceFolderUri));
        if (client.configuration.CurrentConfiguration?.compileCommands || client.configuration.CurrentConfiguration?.configurationProvider) {
            return;
        }
        const rootFolder: vscode.WorkspaceFolder | undefined = client.RootFolder;
        if (!rootFolder) {
            return;
        }

        const ask: PersistentFolderState<boolean> = new PersistentFolderState<boolean>("CPP.showCompileCommandsSelection", true, rootFolder);
        if (!ask.Value) {
            return;
        }

        const aCompileCommandsFile: string = localize("a.compile.commands.file", "a compile_commands.json file");
        const compileCommandStr: string = params.paths.length > 1 ? aCompileCommandsFile : params.paths[0];
        const message: string = (vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders.length > 1)
            ? localize("auto-configure.intellisense.folder", "Would you like to use {0} to auto-configure IntelliSense for the '{1}' folder?", compileCommandStr, client.Name)
            : localize("auto-configure.intellisense.this.folder", "Would you like to use {0} to auto-configure IntelliSense for this folder?", compileCommandStr);

        ui.showConfigureCompileCommandsMessage(async () => {
            const yes: string = localize("yes.button", "Yes");
            const no: string = localize("no.button", "No");
            const askLater: string = localize("ask.me.later.button", "Ask Me Later");
            return vscode.window.showInformationMessage(message, yes, no, askLater).then(async (value) => {
                switch (value) {
                    case yes:
                        if (params.paths.length > 1) {
                            const index: number = await ui.showCompileCommands(params.paths);
                            if (index < 0) {
                                return false;
                            }
                            this.configuration.setCompileCommands(params.paths[index]);
                        } else {
                            this.configuration.setCompileCommands(params.paths[0]);
                        }
                        return true;
                    case askLater:
                        break;
                    case no:
                        ask.Value = false;
                        break;
                }
                return false;
            });
        },
        () => ask.Value = false);
    }

    /**
     * requests to the language server
     */
    public requestSwitchHeaderSource(rootPath: string, fileName: string): Thenable<string> {
        const params: SwitchHeaderSourceParams = {
            switchHeaderSourceFileName: fileName,
            workspaceFolderUri: rootPath
        };
        return this.requestWhenReady(() => this.languageClient.sendRequest(SwitchHeaderSourceRequest, params));
    }

    /**
     * notifications to the language server
     */
    public activeDocumentChanged(document: vscode.TextDocument): void {
        this.notifyWhenLanguageClientReady(() => {
            this.languageClient.sendNotification(ActiveDocumentChangeNotification, this.languageClient.code2ProtocolConverter.asTextDocumentIdentifier(document));
        });
    }

    /**
     * enable UI updates from this client and resume tag parsing on the server.
     */
    public activate(): void {
        this.model.activate();
        this.resumeParsing();
    }

    public selectionChanged(selection: Range): void {
        this.notifyWhenLanguageClientReady(() => {
            this.languageClient.sendNotification(TextEditorSelectionChangeNotification, selection);
        });
    }

    public resetDatabase(): void {
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(ResetDatabaseNotification));
    }

    /**
     * disable UI updates from this client and pause tag parsing on the server.
     */
    public deactivate(): void {
        this.model.deactivate();
    }

    public pauseParsing(): void {
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(PauseParsingNotification));
    }

    public resumeParsing(): void {
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(ResumeParsingNotification));
    }

    private doneInitialCustomBrowseConfigurationCheck: Boolean = false;

    private onConfigurationsChanged(cppProperties: configs.CppProperties): void {
        if (!cppProperties.Configurations) {
            return;
        }
        const configurations: configs.Configuration[] = cppProperties.Configurations;
        const params: CppPropertiesParams = {
            configurations: configurations,
            currentConfiguration: this.configuration.CurrentConfigurationIndex,
            workspaceFolderUri: this.RootPath,
            isReady: true
        };
        // Separate compiler path and args before sending to language client
        params.configurations.forEach((c: configs.Configuration) => {
            const compilerPathAndArgs: util.CompilerPathAndArgs =
                util.extractCompilerPathAndArgs(c.compilerPath, c.compilerArgs);
            c.compilerPath = compilerPathAndArgs.compilerPath;
            c.compilerArgs = compilerPathAndArgs.additionalArgs;
        });
        this.languageClient.sendNotification(ChangeCppPropertiesNotification, params);
        const lastCustomBrowseConfigurationProviderId: PersistentFolderState<string | undefined> | undefined = cppProperties.LastCustomBrowseConfigurationProviderId;
        const lastCustomBrowseConfiguration: PersistentFolderState<WorkspaceBrowseConfiguration | undefined> | undefined = cppProperties.LastCustomBrowseConfiguration;
        if (!!lastCustomBrowseConfigurationProviderId && !!lastCustomBrowseConfiguration) {
            if (!this.doneInitialCustomBrowseConfigurationCheck) {
                // Send the last custom browse configuration we received from this provider.
                // This ensures we don't start tag parsing without it, and undo'ing work we have to re-do when the (likely same) browse config arrives
                // Should only execute on launch, for the initial delivery of configurations
                if (lastCustomBrowseConfiguration.Value) {
                    this.sendCustomBrowseConfiguration(lastCustomBrowseConfiguration.Value, lastCustomBrowseConfigurationProviderId.Value);
                    params.isReady = false;
                }
                this.doneInitialCustomBrowseConfigurationCheck = true;
            }
        }
        const configName: string | undefined = configurations[params.currentConfiguration].name ?? "";
        this.model.activeConfigName.setValueIfActive(configName);
        const newProvider: string | undefined = this.configuration.CurrentConfigurationProvider;
        if (!isSameProviderExtensionId(newProvider, this.configurationProvider)) {
            if (this.configurationProvider) {
                this.clearCustomBrowseConfiguration();
            }
            this.configurationProvider = newProvider;
            this.updateCustomBrowseConfiguration();
            this.updateCustomConfigurations();
        }
    }

    private onSelectedConfigurationChanged(index: number): void {
        const params: FolderSelectedSettingParams = {
            currentConfiguration: index,
            workspaceFolderUri: this.RootPath
        };
        this.notifyWhenLanguageClientReady(() => {
            this.languageClient.sendNotification(ChangeSelectedSettingNotification, params);
            let configName: string = "";
            if (this.configuration.ConfigurationNames) {
                configName = this.configuration.ConfigurationNames[index];
            }
            this.model.activeConfigName.Value = configName;
            this.configuration.onDidChangeSettings();
        });
    }

    private onCompileCommandsChanged(path: string): void {
        const params: FileChangedParams = {
            uri: vscode.Uri.file(path).toString(),
            workspaceFolderUri: this.RootPath
        };
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(ChangeCompileCommandsNotification, params));
    }

    private isSourceFileConfigurationItem(input: any, providerVersion: Version): input is SourceFileConfigurationItem {
        // IntelliSenseMode and standard are optional for version 5+.
        let areOptionalsValid: boolean = false;
        if (providerVersion < Version.v5) {
            areOptionalsValid = util.isString(input.configuration.intelliSenseMode) && util.isString(input.configuration.standard);
        } else {
            areOptionalsValid = util.isOptionalString(input.configuration.intelliSenseMode) && util.isOptionalString(input.configuration.standard);
        }
        return (input && (util.isString(input.uri) || util.isUri(input.uri)) &&
            input.configuration &&
            areOptionalsValid &&
            util.isArrayOfString(input.configuration.includePath) &&
            util.isArrayOfString(input.configuration.defines) &&
            util.isOptionalArrayOfString(input.configuration.compilerArgs) &&
            util.isOptionalArrayOfString(input.configuration.forcedInclude));
    }

    private sendCustomConfigurations(configs: any, providerVersion: Version): void {
        // configs is marked as 'any' because it is untrusted data coming from a 3rd-party. We need to sanitize it before sending it to the language server.
        if (!configs || !(configs instanceof Array)) {
            console.warn("discarding invalid SourceFileConfigurationItems[]: " + configs);
            return;
        }

        const settings: CppSettings = new CppSettings();
        const out: logger.Logger = logger.getOutputChannelLogger();
        if (settings.loggingLevel === "Debug") {
            out.appendLine(localize("configurations.received", "Custom configurations received:"));
        }
        const sanitized: SourceFileConfigurationItemAdapter[] = [];
        configs.forEach(item => {
            if (this.isSourceFileConfigurationItem(item, providerVersion)) {
                this.configurationLogging.set(item.uri.toString(), JSON.stringify(item.configuration, null, 4));
                if (settings.loggingLevel === "Debug") {
                    out.appendLine(`  uri: ${item.uri.toString()}`);
                    out.appendLine(`  config: ${JSON.stringify(item.configuration, null, 2)}`);
                }
                if (item.configuration.includePath.some(path => path.endsWith('**'))) {
                    console.warn("custom include paths should not use recursive includes ('**')");
                }
                // Separate compiler path and args before sending to language client
                const itemConfig: util.Mutable<SourceFileConfiguration> = { ...item.configuration };
                if (util.isString(itemConfig.compilerPath)) {
                    const compilerPathAndArgs: util.CompilerPathAndArgs = util.extractCompilerPathAndArgs(
                        itemConfig.compilerPath,
                        util.isArrayOfString(itemConfig.compilerArgs) ? itemConfig.compilerArgs : undefined);
                    itemConfig.compilerPath = compilerPathAndArgs.compilerPath;
                    itemConfig.compilerArgs = compilerPathAndArgs.additionalArgs;
                }
                sanitized.push({
                    uri: item.uri.toString(),
                    configuration: itemConfig
                });
            } else {
                console.warn("discarding invalid SourceFileConfigurationItem: " + JSON.stringify(item));
            }
        });

        if (sanitized.length === 0) {
            return;
        }

        const params: CustomConfigurationParams = {
            configurationItems: sanitized,
            workspaceFolderUri: this.RootPath
        };

        this.languageClient.sendNotification(CustomConfigurationNotification, params);
    }

    private browseConfigurationLogging: string = "";
    private configurationLogging: Map<string, string> = new Map<string, string>();

    private isWorkspaceBrowseConfiguration(input: any): boolean {
        return util.isArrayOfString(input.browsePath) &&
            util.isOptionalString(input.compilerPath) &&
            util.isOptionalString(input.standard) &&
            util.isOptionalArrayOfString(input.compilerArgs) &&
            util.isOptionalString(input.windowsSdkVersion);
    }

    private sendCustomBrowseConfiguration(config: any, providerId?: string, timeoutOccured?: boolean): void {
        const rootFolder: vscode.WorkspaceFolder | undefined = this.RootFolder;
        if (!rootFolder) {
            return;
        }
        const lastCustomBrowseConfiguration: PersistentFolderState<WorkspaceBrowseConfiguration | undefined> = new PersistentFolderState<WorkspaceBrowseConfiguration | undefined>("CPP.lastCustomBrowseConfiguration", undefined, rootFolder);
        const lastCustomBrowseConfigurationProviderId: PersistentFolderState<string | undefined> = new PersistentFolderState<string | undefined>("CPP.lastCustomBrowseConfigurationProviderId", undefined, rootFolder);
        let sanitized: util.Mutable<WorkspaceBrowseConfiguration>;

        this.browseConfigurationLogging = "";

        // This while (true) is here just so we can break out early if the config is set on error
        while (true) {
            // config is marked as 'any' because it is untrusted data coming from a 3rd-party. We need to sanitize it before sending it to the language server.
            if (timeoutOccured || !config || config instanceof Array) {
                if (!timeoutOccured) {
                    console.log("Received an invalid browse configuration from configuration provider.");
                }
                const configValue: WorkspaceBrowseConfiguration | undefined = lastCustomBrowseConfiguration.Value;
                if (configValue) {
                    sanitized = configValue;
                    console.log("Falling back to last received browse configuration: ", JSON.stringify(sanitized, null, 2));
                    break;
                }
                console.log("No browse configuration is available.");
                return;
            }

            sanitized = { ...<WorkspaceBrowseConfiguration>config };
            if (!this.isWorkspaceBrowseConfiguration(sanitized)) {
                console.log("Received an invalid browse configuration from configuration provider: " + JSON.stringify(sanitized));
                const configValue: WorkspaceBrowseConfiguration | undefined = lastCustomBrowseConfiguration.Value;
                if (configValue) {
                    sanitized = configValue;
                    console.log("Falling back to last received browse configuration: ", JSON.stringify(sanitized, null, 2));
                    break;
                }
                return;
            }

            const settings: CppSettings = new CppSettings();
            if (settings.loggingLevel === "Debug") {
                const out: logger.Logger = logger.getOutputChannelLogger();
                out.appendLine(localize("browse.configuration.received", "Custom browse configuration received: {0}", JSON.stringify(sanitized, null, 2)));
            }

            // Separate compiler path and args before sending to language client
            if (util.isString(sanitized.compilerPath)) {
                const compilerPathAndArgs: util.CompilerPathAndArgs = util.extractCompilerPathAndArgs(
                    sanitized.compilerPath,
                    util.isArrayOfString(sanitized.compilerArgs) ? sanitized.compilerArgs : undefined);
                sanitized.compilerPath = compilerPathAndArgs.compilerPath;
                sanitized.compilerArgs = compilerPathAndArgs.additionalArgs;
            }

            lastCustomBrowseConfiguration.Value = sanitized;
            if (!providerId) {
                lastCustomBrowseConfigurationProviderId.setDefault();
            } else {
                lastCustomBrowseConfigurationProviderId.Value = providerId;
            }
            break;
        }

        this.browseConfigurationLogging = `Custom browse configuration: \n${JSON.stringify(sanitized, null, 4)}\n`;

        const params: CustomBrowseConfigurationParams = {
            browseConfiguration: sanitized,
            workspaceFolderUri: this.RootPath
        };

        this.languageClient.sendNotification(CustomBrowseConfigurationNotification, params);
    }

    private clearCustomConfigurations(): void {
        this.configurationLogging.clear();
        const params: WorkspaceFolderParams = {
            workspaceFolderUri: this.RootPath
        };
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(ClearCustomConfigurationsNotification, params));
    }

    private clearCustomBrowseConfiguration(): void {
        this.browseConfigurationLogging = "";
        const params: WorkspaceFolderParams = {
            workspaceFolderUri: this.RootPath
        };
        this.notifyWhenLanguageClientReady(() => this.languageClient.sendNotification(ClearCustomBrowseConfigurationNotification, params));
    }

    /**
     * command handlers
     */
    public async handleConfigurationSelectCommand(): Promise<void> {
        await this.awaitUntilLanguageClientReady();
        const configNames: string[] | undefined = this.configuration.ConfigurationNames;
        if (configNames) {
            const index: number = await ui.showConfigurations(configNames);
            if (index < 0) {
                return;
            }
            this.configuration.select(index);
        }
    }

    public async handleConfigurationProviderSelectCommand(): Promise<void> {
        await this.awaitUntilLanguageClientReady();
        const extensionId: string | undefined = await ui.showConfigurationProviders(this.configuration.CurrentConfigurationProvider);
        if (extensionId === undefined) {
            // operation was canceled.
            return;
        }
        await this.configuration.updateCustomConfigurationProvider(extensionId);
        if (extensionId) {
            const provider: CustomConfigurationProvider1 | undefined = getCustomConfigProviders().get(extensionId);
            this.updateCustomBrowseConfiguration(provider);
            this.updateCustomConfigurations(provider);
            telemetry.logLanguageServerEvent("customConfigurationProvider", { "providerId": extensionId });
        } else {
            this.clearCustomConfigurations();
            this.clearCustomBrowseConfiguration();
        }
    }

    public async handleShowParsingCommands(): Promise<void> {
        await this.awaitUntilLanguageClientReady();
        const index: number = await ui.showParsingCommands();
        if (index === 0) {
            this.pauseParsing();
        } else if (index === 1) {
            this.resumeParsing();
        }
    }

    public handleConfigurationEditCommand(viewColumn: vscode.ViewColumn = vscode.ViewColumn.Active): void {
        this.notifyWhenLanguageClientReady(() => this.configuration.handleConfigurationEditCommand(undefined, vscode.window.showTextDocument, viewColumn));
    }

    public handleConfigurationEditJSONCommand(viewColumn: vscode.ViewColumn = vscode.ViewColumn.Active): void {
        this.notifyWhenLanguageClientReady(() => this.configuration.handleConfigurationEditJSONCommand(undefined, vscode.window.showTextDocument, viewColumn));
    }

    public handleConfigurationEditUICommand(viewColumn: vscode.ViewColumn = vscode.ViewColumn.Active): void {
        this.notifyWhenLanguageClientReady(() => this.configuration.handleConfigurationEditUICommand(undefined, vscode.window.showTextDocument, viewColumn));
    }

    public handleAddToIncludePathCommand(path: string): void {
        this.notifyWhenLanguageClientReady(() => this.configuration.addToIncludePathCommand(path));
    }

    public async handleGoToDirectiveInGroup(next: boolean): Promise<void> {
        const editor: vscode.TextEditor | undefined = vscode.window.activeTextEditor;
        if (editor) {
            const params: GoToDirectiveInGroupParams = {
                uri: editor.document.uri.toString(),
                position: editor.selection.active,
                next: next
            };

            const response: Position | undefined = await this.languageClient.sendRequest(GoToDirectiveInGroupRequest, params);
            if (response) {
                const p: vscode.Position = new vscode.Position(response.line, response.character);
                const r: vscode.Range = new vscode.Range(p, p);

                // Check if still the active document.
                const currentEditor: vscode.TextEditor | undefined = vscode.window.activeTextEditor;
                if (currentEditor && editor.document.uri === currentEditor.document.uri) {
                    currentEditor.selection = new vscode.Selection(r.start, r.end);
                    currentEditor.revealRange(r);
                }
            }
        }
    }

    public async handleCheckForCompiler(): Promise<void> {
        await this.awaitUntilLanguageClientReady();
        const compilers: configs.KnownCompiler[] | undefined = await this.getKnownCompilers();
        if (!compilers || compilers.length === 0) {
            const compilerName: string = process.platform === "win32" ? "MSVC" : (process.platform === "darwin" ? "Clang" : "GCC");
            vscode.window.showInformationMessage(localize("no.compilers.found", "No C++ compilers were found on your system. For your platform, we recommend installing {0} using the instructions in the editor.", compilerName), { modal: true });
        } else {
            const header: string = localize("compilers.found", "We found the following C++ compiler(s) on your system:");
            let message: string = header + "\n";
            const settings: CppSettings = new CppSettings(this.RootUri);
            const pathSeparator: string | undefined = settings.preferredPathSeparator;
            compilers.forEach(compiler => {
                if (pathSeparator !== "Forward Slash") {
                    message += "\n" + compiler.path.replace(/\//g, '\\');
                } else {
                    message += "\n" + compiler.path.replace(/\\/g, '/');
                }
            });
            if (compilers.length > 1) {
                message += "\n\n" + localize("compilers.found.message", "You can specify which compiler to use in your project's IntelliSense Configuration.");
            }
            vscode.window.showInformationMessage(message, { modal: true });
        }
    }

    public onInterval(): void {
        // These events can be discarded until the language client is ready.
        // Don't queue them up with this.notifyWhenLanguageClientReady calls.
        if (this.innerLanguageClient !== undefined && this.configuration !== undefined) {
            this.languageClient.sendNotification(IntervalTimerNotification);
            this.configuration.checkCppProperties();
            this.configuration.checkCompileCommands();
        }
    }

    public dispose(): void {
        this.disposables.forEach((d) => d.dispose());
        this.disposables = [];
        if (this.documentFormattingProviderDisposable) {
            this.documentFormattingProviderDisposable.dispose();
            this.documentFormattingProviderDisposable = undefined;
        }
        if (this.formattingRangeProviderDisposable) {
            this.formattingRangeProviderDisposable.dispose();
            this.formattingRangeProviderDisposable = undefined;
        }
        if (this.onTypeFormattingProviderDisposable) {
            this.onTypeFormattingProviderDisposable.dispose();
            this.onTypeFormattingProviderDisposable = undefined;
        }
        if (this.codeFoldingProviderDisposable) {
            this.codeFoldingProviderDisposable.dispose();
            this.codeFoldingProviderDisposable = undefined;
        }
        if (this.semanticTokensProviderDisposable) {
            this.semanticTokensProviderDisposable.dispose();
            this.semanticTokensProviderDisposable = undefined;
        }
        this.model.dispose();
    }

    public static stopLanguageClient(): Thenable<void> {
        return languageClient ? languageClient.stop() : Promise.resolve();
    }

    public handleReferencesIcon(): void {
        this.notifyWhenLanguageClientReady(() => {
            const cancelling: boolean = DefaultClient.referencesPendingCancellations.length > 0;
            if (!cancelling) {
                workspaceReferences.UpdateProgressUICounter(this.model.referencesCommandMode.Value);
                if (this.ReferencesCommandMode === refs.ReferencesCommandMode.Find) {
                    if (!workspaceReferences.referencesRequestPending) {
                        if (workspaceReferences.referencesRequestHasOccurred) {
                            // References are not usable if a references request is pending,
                            // So after the initial request, we don't send a 2nd references request until the next request occurs.
                            if (!workspaceReferences.referencesRefreshPending) {
                                workspaceReferences.referencesRefreshPending = true;
                                vscode.commands.executeCommand("references-view.refresh");
                            }
                        } else {
                            workspaceReferences.referencesRequestHasOccurred = true;
                            workspaceReferences.referencesRequestPending = true;
                            this.languageClient.sendNotification(RequestReferencesNotification, false);
                        }
                    }
                }
            }
        });
    }

    public cancelReferences(): void {
        DefaultClient.referencesParams = undefined;
        DefaultClient.renamePending = false;
        if (DefaultClient.referencesRequestPending || workspaceReferences.symbolSearchInProgress) {
            const cancelling: boolean = DefaultClient.referencesPendingCancellations.length > 0;
            DefaultClient.referencesPendingCancellations.push({
                reject: () => { },
                callback: () => { }
            });
            if (!cancelling) {
                workspaceReferences.referencesCanceled = true;
                languageClient.sendNotification(CancelReferencesNotification);
            }
        }
    }

    private handleReferencesProgress(notificationBody: refs.ReportReferencesProgressNotification): void {
        workspaceReferences.handleProgress(notificationBody);
    }

    private processReferencesResult(referencesResult: refs.ReferencesResult): void {
        workspaceReferences.processResults(referencesResult);
    }

    public setReferencesCommandMode(mode: refs.ReferencesCommandMode): void {
        this.model.referencesCommandMode.Value = mode;
    }

    public abortRequest(id: number): void {
        const params: AbortRequestParams = {
            id: id
        };
        languageClient.sendNotification(AbortRequestNotification, params);
    }
}

function getLanguageServerFileName(): string {
    let extensionProcessName: string = 'cpptools';
    const plat: NodeJS.Platform = process.platform;
    if (plat === 'win32') {
        extensionProcessName += '.exe';
    } else if (plat !== 'linux' && plat !== 'darwin') {
        throw "Invalid Platform";
    }
    return path.resolve(util.getExtensionFilePath("bin"), extensionProcessName);
}

class NullClient implements Client {
    private booleanEvent = new vscode.EventEmitter<boolean>();
    private stringEvent = new vscode.EventEmitter<string>();
    private referencesCommandModeEvent = new vscode.EventEmitter<refs.ReferencesCommandMode>();

    public get TagParsingChanged(): vscode.Event<boolean> { return this.booleanEvent.event; }
    public get IntelliSenseParsingChanged(): vscode.Event<boolean> { return this.booleanEvent.event; }
    public get ReferencesCommandModeChanged(): vscode.Event<refs.ReferencesCommandMode> { return this.referencesCommandModeEvent.event; }
    public get TagParserStatusChanged(): vscode.Event<string> { return this.stringEvent.event; }
    public get ActiveConfigChanged(): vscode.Event<string> { return this.stringEvent.event; }
    RootPath: string = "/";
    RootRealPath: string = "/";
    RootUri?: vscode.Uri = vscode.Uri.file("/");
    Name: string = "(empty)";
    TrackedDocuments = new Set<vscode.TextDocument>();
    onDidChangeSettings(event: vscode.ConfigurationChangeEvent, isFirstClient: boolean): { [key: string]: string } { return {}; }
    onDidOpenTextDocument(document: vscode.TextDocument): void { }
    onDidCloseTextDocument(document: vscode.TextDocument): void { }
    onDidChangeVisibleTextEditors(editors: vscode.TextEditor[]): void { }
    onDidChangeTextDocument(textDocumentChangeEvent: vscode.TextDocumentChangeEvent): void { }
    onRegisterCustomConfigurationProvider(provider: CustomConfigurationProvider1): Thenable<void> { return Promise.resolve(); }
    updateCustomConfigurations(requestingProvider?: CustomConfigurationProvider1): Thenable<void> { return Promise.resolve(); }
    updateCustomBrowseConfiguration(requestingProvider?: CustomConfigurationProvider1): Thenable<void> { return Promise.resolve(); }
    provideCustomConfiguration(docUri: vscode.Uri, requestFile?: string): Promise<void> { return Promise.resolve(); }
    logDiagnostics(): Promise<void> { return Promise.resolve(); }
    rescanFolder(): Promise<void> { return Promise.resolve(); }
    toggleReferenceResultsView(): void { }
    setCurrentConfigName(configurationName: string): Thenable<void> { return Promise.resolve(); }
    getCurrentConfigName(): Thenable<string> { return Promise.resolve(""); }
    getCurrentConfigCustomVariable(variableName: string): Thenable<string> { return Promise.resolve(""); }
    getVcpkgInstalled(): Thenable<boolean> { return Promise.resolve(false); }
    getVcpkgEnabled(): Thenable<boolean> { return Promise.resolve(false); }
    getCurrentCompilerPathAndArgs(): Thenable<util.CompilerPathAndArgs | undefined> { return Promise.resolve(undefined); }
    getKnownCompilers(): Thenable<configs.KnownCompiler[] | undefined> { return Promise.resolve([]); }
    takeOwnership(document: vscode.TextDocument): void { }
    queueTask<T>(task: () => Thenable<T>): Promise<T> { return Promise.resolve(task()); }
    requestWhenReady<T>(request: () => Thenable<T>): Thenable<T> { return request(); }
    notifyWhenLanguageClientReady(notify: () => void): void { }
    awaitUntilLanguageClientReady(): void { }
    requestSwitchHeaderSource(rootPath: string, fileName: string): Thenable<string> { return Promise.resolve(""); }
    activeDocumentChanged(document: vscode.TextDocument): void { }
    activate(): void { }
    selectionChanged(selection: Range): void { }
    resetDatabase(): void { }
    deactivate(): void { }
    pauseParsing(): void { }
    resumeParsing(): void { }
    handleConfigurationSelectCommand(): Promise<void> { return Promise.resolve(); }
    handleConfigurationProviderSelectCommand(): Promise<void> { return Promise.resolve(); }
    handleShowParsingCommands(): Promise<void> { return Promise.resolve(); }
    handleReferencesIcon(): void { }
    handleConfigurationEditCommand(viewColumn?: vscode.ViewColumn): void { }
    handleConfigurationEditJSONCommand(viewColumn?: vscode.ViewColumn): void { }
    handleConfigurationEditUICommand(viewColumn?: vscode.ViewColumn): void { }
    handleAddToIncludePathCommand(path: string): void { }
    handleGoToDirectiveInGroup(next: boolean): Promise<void> { return Promise.resolve(); }
    handleCheckForCompiler(): Promise<void> { return Promise.resolve(); }
    onInterval(): void { }
    dispose(): void {
        this.booleanEvent.dispose();
        this.stringEvent.dispose();
    }
    addFileAssociations(fileAssociations: string, languageId: string): void { }
    sendDidChangeSettings(settings: any): void { }
}
